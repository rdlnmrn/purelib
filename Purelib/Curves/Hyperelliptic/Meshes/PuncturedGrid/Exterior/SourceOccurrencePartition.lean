module
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourcePathComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! The retained occurrence slices partition the original closed source bank.
Repeated parents retain their positions; neither set equality nor a new source
preparation is used. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryParentLocation (occurrenceParents)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation (occurrenceAt)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.PairedIncrementArea (area)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Equality of the natural-value lists identifies the exact original bounded-index lists. -/
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

/-- The offset bounded-index enumeration is the corresponding consecutive natural range. -/
private theorem ofFn_range (count offset : Nat) :
    List.ofFn (fun i : Fin count => offset + i.val) = List.range' offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ]
    apply congrArg (List.cons offset)
    exact (OfFn.Basic.ofFn_congr (fun i : Fin count =>
      (Nat.add_assoc offset i.val 1).symm.trans (Nat.add_right_comm offset i.val 1))).trans (ih (offset + 1))

/-- Enumerating the retained bounded positions reconstructs the exact original list. -/
private theorem ofFn_read {α : Type u} (values : List α) {count : Nat}
    (length : values.length = count) :
    List.ofFn (fun i : Fin count => values[i.val]'(i.isLt.trans_eq length.symm)) = values := by
  cases length
  exact OfFn.Basic.ofFn_getElem values

/-- The finite Gaussian sum of pointwise differences equals the difference of the original sums. -/
private theorem sum_difference {count : Nat} (left right : Fin count → InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => left i - right i)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn left) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (List.ofFn right) := by
  induction count with
  | zero => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ, OfFn.Basic.ofFn_succ (function := left),
      OfFn.Basic.ofFn_succ (function := right)]
    change (left 0 - right 0) + _ = (left 0 + _) - (right 0 + _)
    rw [ih]
    ring1

/-- Subtracting a certified scalar discrepancy recovers the retained reference value. -/
private theorem subtract_remainder {source reference remainder : InverseRootPolynomial.Gaussian}
    (difference : source - reference = remainder) : source - remainder = reference := by
  rw [← difference]
  ring1

/-- Pointwise equality of original block lengths gives equality of their complete flattened lengths. -/
private theorem flatten_length_congr {α β : Type} {count : Nat}
    (left : Fin count → List α) (right : Fin count → List β)
    (lengths : ∀ i, (left i).length = (right i).length) :
    (List.ofFn left).flatten.length = (List.ofFn right).flatten.length := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ, OfFn.Basic.ofFn_succ (function := right),
      List.flatten_cons, List.flatten_cons, Data.List.Append.length_append, Data.List.Append.length_append]
    exact congrArg₂ Nat.add (lengths 0) (ih _ _ (fun i => lengths i.succ))

/-- Summing the original flattened block bank equals the sum of the retained block sums. -/
private theorem sum_flatten_ofFn {count : Nat} (blocks : Fin count → List InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn blocks).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun i => Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (blocks i))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ, List.flatten_cons, IncrementArea.sum_append,
      OfFn.Basic.ofFn_succ]
    exact congrArg (fun tail => Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks 0) + tail) (ih _)

/-- Bounds on every value in every original indexed block hold throughout the flattened block bank. -/
private theorem flattened_bounds {count : Nat} (blocks : Fin count → List InverseRootPolynomial.Gaussian) {bound :
  InverseRootPolynomial.Coordinate}
    (bounds : ∀ i value, value ∈ blocks i → Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
    ∀ value ∈ (List.ofFn blocks).flatten, Data.Gaussian.Norm.Basic.normSq value ≤ bound := by
  induction count with
  | zero => intro value member; cases member
  | succ count ih =>
    intro value member
    rw [OfFn.Basic.ofFn_succ, List.flatten_cons] at member
    rcases Data.List.Membership.mem_append.mp member with head | tail
    · exact bounds 0 value head
    · exact ih _ (fun i => bounds i.succ) value tail

/-- Apply the physical side's orientation to a complete area difference. -/
theorem orient_source_difference (forward : Bool) (source reference remainder canonical :
  InverseRootPolynomial.Gaussian)
    (difference : source - reference = remainder)
    (orientation : (if forward then reference else -reference) = canonical) :
    (if forward then source else -source) - canonical =
      if forward then remainder else -remainder := by
  cases forward with
  | true => exact (congrArg (fun value => source - value) orientation.symm).trans difference
  | false =>
    rw [← orientation, ← difference]
    change -source - -reference = -(source - reference)
    ring1

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

/-- The original occurrence parent ranges concatenate to the complete retained parent range in exact order. -/
private theorem occurrence_ranges (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential))
    (offset : Nat) :
    (List.ofFn (fun outer : Fin occurrences.length =>
      List.range' (offset + (BoundaryParentLocation.occurrenceParents (occurrences.take outer.val)).length)
        (BoundaryAxisLocation.occurrenceAt occurrences outer).compared.entered.cache.parents.length)).flatten =
      List.range' offset (BoundaryParentLocation.occurrenceParents occurrences).length := by
  induction occurrences generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    rw [OfFn.Basic.ofFn_succ, List.flatten_cons]
    change List.range' offset head.compared.entered.cache.parents.length ++
      (List.ofFn (fun i : Fin tail.length =>
        List.range' (offset + (head.compared.entered.cache.parents ++ BoundaryParentLocation.occurrenceParents
          (tail.take i.val)).length)
          (BoundaryAxisLocation.occurrenceAt tail i).compared.entered.cache.parents.length)).flatten =
      List.range' offset (head.compared.entered.cache.parents ++ BoundaryParentLocation.occurrenceParents tail).length
    have tails := OfFn.Basic.ofFn_congr (fun i : Fin tail.length =>
      congrArg (fun start => List.range' start (BoundaryAxisLocation.occurrenceAt tail
        i).compared.entered.cache.parents.length)
        ((congrArg (fun n => offset + n) (Data.List.Append.length_append ..)).trans
          (Nat.add_assoc offset head.compared.entered.cache.parents.length
            (BoundaryParentLocation.occurrenceParents (tail.take i.val)).length).symm))
    exact (congrArg (List.append (List.range' offset head.compared.entered.cache.parents.length))
      ((congrArg List.flatten tails).trans (ih (offset + head.compared.entered.cache.parents.length)))).trans
      (Data.List.Range.Basic.range'_append_1.trans (congrArg (List.range' offset) (Data.List.Append.length_append
        ..).symm))

variable {program : ExteriorProgram lifted
  differential} {prepared :
  ExteriorProgram.SurfacePreparation
  regular domains program}
  {requested : Coordinate} {minimum : Nat}

/-- Exact ordered partition of all original bank positions. -/
theorem parentIndices_partition (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    (List.ofFn (comparison.parentIndices)).flatten =
      List.ofFn (fun i : Fin comparison.original.plans.length => i) := by
  apply
    fin_values_injective
  rw [Data.List.Flatten.map_flatten, OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
  have parts := OfFn.Basic.ofFn_congr (comparison.parentIndices_values)
  have ranged :=
    occurrence_ranges
    prepared.occurrences 0
  have count : (BoundaryParentLocation.occurrenceParents prepared.occurrences).length = comparison.original.plans.length
    := by
    exact (congrArg List.length (show BoundaryParentLocation.occurrenceParents prepared.occurrences =
      comparison.original.plans.map (fun plan => plan.parent) from
        prepared.parents_eq.trans comparison.original.parents_eq.symm)).trans (Data.List.Map.length_map ..)
  have all :=
    ofFn_range
    comparison.original.plans.length 0
  have zeros := OfFn.Basic.ofFn_congr (fun outer : Fin prepared.occurrences.length =>
    congrArg (fun start => List.range' start (BoundaryAxisLocation.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
      (Nat.zero_add (BoundaryParentLocation.occurrenceParents (prepared.occurrences.take outer.val)).length))
  have indices := OfFn.Basic.ofFn_congr (fun i : Fin comparison.original.plans.length => Nat.zero_add i.val)
  exact (congrArg List.flatten parts).trans ((congrArg List.flatten zeros).symm.trans
    (ranged.trans ((congrArg (List.range' 0) count).trans (all.symm.trans indices))))

/-- Aggregate all original-parent errors in one finite sum, using the retained occurrence partition rather than
multiplying two worst-case counts. -/
theorem component_resampling_bound (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (blocks : Fin prepared.occurrences.length → List InverseRootPolynomial.Gaussian)
    (errors : Fin prepared.occurrences.length → InverseRootPolynomial.Gaussian)
    (readback : ∀ outer, Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks outer) = errors outer)
    (lengths : ∀ outer, (blocks outer).length = (comparison.parentIndices outer).length)
    {bound : InverseRootPolynomial.Coordinate} (bounds : ∀ outer value, value ∈ blocks outer →
      Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn errors)) ≤
      (comparison.original.plans.length : InverseRootPolynomial.Coordinate)^2 * bound := by
  have count :=
    (flatten_length_congr
    blocks comparison.parentIndices lengths).trans
    ((congrArg List.length comparison.parentIndices_partition).trans Data.List.OfFn.Basic.length_ofFn)
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le (List.ofFn blocks).flatten bound

      (flattened_bounds
      blocks bounds)
  have sums :=
    (sum_flatten_ofFn
    blocks).trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (OfFn.Basic.ofFn_congr readback))
  rw [sums, count] at estimate
  exact estimate.trans_eq (by ring1)

/-- The forward occurrence blocks are the actual bank, with every original entry exactly once and in its original order.
-/
theorem sourceOccurrenceBlocks_partition (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    (List.ofFn (fun outer => comparison.sourceOccurrenceBlocks outer true)).flatten =
      comparison.sourcePaths := by
  let bank := comparison.sourcePaths
  have length : bank.length = comparison.original.plans.length := Data.List.OfFn.Basic.length_ofFn
  let read := fun i : Fin comparison.original.plans.length => bank[i.val]'(i.isLt.trans_eq length.symm)
  have parts := OfFn.Basic.ofFn_congr (fun outer : Fin prepared.occurrences.length =>
    (show comparison.sourceOccurrenceBlocks outer true = (comparison.parentIndices outer).map read from rfl))
  have all := congrArg (List.map read) comparison.parentIndices_partition
  rw [Data.List.Flatten.map_flatten, OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn] at all
  apply (congrArg List.flatten parts).trans
  apply all.trans
  exact
    ofFn_read
    bank length

/-- Flattening all original forward occurrence paths reconstructs the complete retained source increment list. -/
theorem sourceOccurrencePaths_partition (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    (List.ofFn (fun outer => (comparison.sourceOccurrenceBlocks outer true).flatten)).flatten =
      comparison.sourcePaths.flatten := by
  have all := congrArg List.flatten comparison.sourceOccurrenceBlocks_partition
  rw [Data.List.Flatten.flatten_flatten, OfFn.Basic.map_ofFn] at all
  exact all

/-- All occurrence interiors and their joining polygon reconstruct the original full source area. This is not a sum of
endpoint chords alone. -/
theorem sourceOccurrencePaths_area (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun outer => PairedIncrementArea.area
      (comparison.sourceOccurrenceBlocks outer true).flatten)) +
      PairedIncrementArea.area (List.ofFn (fun outer => PairedIncrementArea.total (comparison.sourceOccurrenceBlocks
        outer true).flatten)) =
        PairedIncrementArea.area comparison.sourcePaths.flatten := by
  have formula := PairedAreaBlocks.area_flatten
    (List.ofFn (fun outer => (comparison.sourceOccurrenceBlocks outer true).flatten))
  rw [OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn] at formula
  exact formula.symm.trans (congrArg PairedIncrementArea.area comparison.sourceOccurrencePaths_partition)

/-- Transfer the original requested bound to all actual occurrence areas, retaining the complete signed resampling
remainder and joining polygon. -/
theorem component_source_bound (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (sources remainders : Fin prepared.occurrences.length → InverseRootPolynomial.Gaussian)
    (differences : ∀ outer, sources outer - PairedIncrementArea.area (comparison.sourceOccurrenceBlocks outer
      true).flatten = remainders outer) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn sources) +
      PairedIncrementArea.area (List.ofFn (fun outer => PairedIncrementArea.total (comparison.sourceOccurrenceBlocks
        outer true).flatten)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn remainders)) < requested := by
  have interiors :=
    (sum_difference
    sources remainders).symm.trans
    (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (OfFn.Basic.ofFn_congr (fun outer =>
      subtract_remainder
      (differences outer))))
  have equal : Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn sources) +
      PairedIncrementArea.area (List.ofFn (fun outer => PairedIncrementArea.total (comparison.sourceOccurrenceBlocks
        outer true).flatten)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn remainders) = PairedIncrementArea.area
          comparison.sourcePaths.flatten := by
    calc
      _ = (Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn sources) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn remainders)) +
          PairedIncrementArea.area (List.ofFn (fun outer => PairedIncrementArea.total (comparison.sourceOccurrenceBlocks
            outer true).flatten)) := by ring1
      _ = _ := (congrArg (fun value => value +
        PairedIncrementArea.area (List.ofFn (fun outer => PairedIncrementArea.total (comparison.sourceOccurrenceBlocks
          outer true).flatten))) interiors).trans
          comparison.sourceOccurrencePaths_area
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_lt comparison.path_bounded

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
