module
import Purelib.Data.List.Membership
import Purelib.Approximation.Gaussian.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Topology.Surface.Cut.WordErrors
import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Word.SignedWord
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Full weighted boundary-word area error

The drift term and the local increment-error term are both paid, including
the prefix count and the complete area-sum count. The bound concerns the
full word matrix: physical-boundary coordinates have not been discarded.
-/

namespace Purelib.Topology.Surface.Cut.WordAreaBounds

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Data

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Cut.WordErrors
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord CutWordEntry)

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

namespace PrimitivePoint.Bounded

/-- Subtracting two primitive points with the same coordinate bound gives a fourfold bound. -/
theorem sub {first last : Stokes.PrimitivePoint} {bound : PrimitiveAreaBounds.AreaCoordinate}
    (left : (PrimitivePoint.Bounded first) bound) (right : (PrimitivePoint.Bounded last) bound) :
    (PrimitivePoint.Bounded ((PrimitivePoint.sub first) last)) (4 * bound) := by
  change Canonical.normSq (first.left - last.left) ≤ 4 * bound ∧
    Canonical.normSq (first.right - last.right) ≤ 4 * bound
  constructor
  · have estimate := Gaussian.Norm.Bounds.normSq_sub_le_two first.left last.left
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
    exact estimate.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left.1 right.1) (by decide)).trans_eq (by
        ring1))
  · have estimate := Gaussian.Norm.Bounds.normSq_sub_le_two first.right last.right
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
    exact estimate.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left.2 right.2) (by decide)).trans_eq (by
        ring1))

/-- Negating a primitive point preserves its coordinate magnitude bound. -/
theorem neg {point : Stokes.PrimitivePoint} {bound : PrimitiveAreaBounds.AreaCoordinate}
    (bounded : (PrimitivePoint.Bounded point) bound) : (PrimitivePoint.Bounded ((PrimitivePoint.sub PrimitivePoint.zero)
      point)) bound := by
  simpa only [PrimitivePoint.Bounded, PrimitivePoint.zero, PrimitivePoint.sub, Gaussian.Basic.zero_sub,
    Canonical.normSq_neg] using bounded

end PrimitivePoint.Bounded

namespace CutWordArea

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea (Step steps word correction)
open Purelib.Topology.Surface.Cut.WordErrors.CutWordArea (ErrorsBounded)

variable {source target count : Nat} {labels : Fin source → Fin target}
  {generators : Data.Vector (Stokes.OrientedEdge source) count}
  {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin count → Stokes.PrimitivePoint}

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- A cached step starts at the modeled endpoint of its literal prefix.

Membership identifies the retained step and splits the original entry list at that occurrence. Its cached start equals
the supplied initial point plus the modeled total of that exact prefix. -/
theorem steps_member_split {entries : List (BoundaryWord.CutWordEntry labels generators)} {start :
  Stokes.PrimitivePoint}
    {step : CutWordArea.Step (labels := labels) (generators := generators) primitive values}
    (member : step ∈ CutWordArea.steps primitive values start entries) :
    ∃ before after, entries = before ++ step.entry :: after ∧
      step.start = start.add (Pairing.linear (Pairing.totalAt (word before)) values) := by
  induction entries generalizing start with
  | nil => exact (List.not_mem_nil member).elim
  | cons entry entries ih =>
      rcases Membership.mem_cons.mp member with same | member
      · cases same
        refine ⟨[], entries, rfl, ?_⟩
        change start = start.add (Pairing.linear (fun _ => 0) values)
        rw [Pairing.linear_zero]
        change start = ⟨start.left + 0, start.right + 0⟩
        rw [Gaussian.Basic.add_zero, Gaussian.Basic.add_zero]
      · obtain ⟨before, after, entriesEq, startEq⟩ := ih member
        refine ⟨entry :: before, after, congrArg (List.cons entry) entriesEq, ?_⟩
        rw [startEq]
        change (start.add (Pairing.linear entry.letter.coefficients values)).add
          (Pairing.linear (Pairing.totalAt (word before)) values) =
          start.add (Pairing.linear (fun index => entry.letter.coefficients index + Pairing.totalAt (word before) index)
            values)
        rw [Pairing.linear_add]
        simp only [PrimitivePoint.add]
        congr 1 <;> ring1

open Purelib.Topology.Surface.Cut.WordAreaBounds in
/-- Uniform local error bounds control every retained step drift by the square of the complete word length.

The retained boundary path supplies the actual prefix endpoint for each cached step. Its provenance split invokes the
same local error bounds with both original word-count factors. -/
theorem steps_drifts_bounded {entries : List (BoundaryWord.CutWordEntry labels generators)} {bound :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : CutWordArea.ErrorsBounded primitive values entries bound) (nonnegative : 0 ≤ bound)
    {first last : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (entries.map CutWordEntry.edge) first
      last)
    (step : CutWordArea.Step (labels := labels) (generators := generators) primitive values)
    (member : step ∈ CutWordArea.steps primitive values (primitive first) entries) :
    (PrimitivePoint.Bounded step.drift) ((entries.length : PrimitiveAreaBounds.AreaCoordinate) * ((entries.length :
      PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  obtain ⟨before, after, entriesEq, startEq⟩ := steps_member_split member
  have splitPath := path
  rw [entriesEq, Map.map_append] at splitPath
  obtain ⟨middle, prefixPath, tail⟩ := PathEndpoints.split_append _ _ splitPath
  cases tail with
  | cons tail =>
      rw [step.drift_eq, startEq]
      exact CutWordArea.prefix_drift_bounded bounded nonnegative entriesEq.symm prefixPath

/-- Binary count conversion keeps large allocation checks executable without enumerating a synthetic word or using unary
casts. -/
@[expose] def areaWeight (magnitude : PrimitiveAreaBounds.AreaCoordinate) (count : Nat) : AreaCoordinate :=
  let n := Aggregate.countCoordinate count
  8 * magnitude * (4 * n * n + 1)

section
open Purelib.Topology.Surface.Cut.WordAreaBounds
/-- The complete word-area error weight is nonnegative for a nonnegative magnitude bound. -/
theorem areaWeight_nonnegative {magnitude : PrimitiveAreaBounds.AreaCoordinate} (nonnegative : 0 ≤ magnitude) (count :
  Nat) :
    0 ≤ areaWeight magnitude count := by
  have countNonnegative : (0 : PrimitiveAreaBounds.AreaCoordinate) ≤ Aggregate.countCoordinate count := by
    rw [Aggregate.countCoordinate_eq]
    exact Cast.Order.natCast_le_direct (Nat.zero_le _)
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) countNonnegative) countNonnegative) (by decide))

/-- Bound the full retained step correction using drift, increment, original endpoint and local error bounds. -/
theorem Step.correction_bounded (step : CutWordArea.Step (labels := labels) (generators := generators) primitive values)
    {magnitude bound : PrimitiveAreaBounds.AreaCoordinate} (count : Nat)
    (drift : (PrimitivePoint.Bounded step.drift) ((count : PrimitiveAreaBounds.AreaCoordinate) * ((count :
      PrimitiveAreaBounds.AreaCoordinate) * bound)))
    (increment : (PrimitivePoint.Bounded step.increment) (4 * magnitude))
    (endpoint : (PrimitivePoint.Bounded (primitive step.entry.edge.start)) magnitude)
    (error : (PrimitivePoint.Bounded step.error) bound) :
    Data.Gaussian.Norm.Basic.normSq step.correction ≤ areaWeight magnitude count * bound := by
  rw [step.correction_eq, Gaussian.Norm.Basic.normSq_eq_canonical]
  have sumEstimate := Gaussian.Norm.Bounds.normSq_add_le_two
    (Stokes.edgeArea step.drift step.increment)
    (Stokes.edgeArea (primitive step.entry.edge.start) step.error)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at sumEstimate
  have estimate := sumEstimate.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (PrimitivePoint.area_bound drift increment) (PrimitivePoint.area_bound endpoint error)) (by decide))
  exact estimate.trans_eq (by rw [areaWeight, Aggregate.countCoordinate_eq]; ring1)

end

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- The retained correction fold equals the Gaussian sum of all original step corrections. -/
theorem correction_eq_sum (samples : List (CutWordArea.Step (labels := labels) (generators := generators) primitive
  values)) :
    CutWordArea.correction samples = Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.map Step.correction) := by
  induction samples with
  | nil => rfl
  | cons step samples ih => exact congrArg (step.correction + ·) ih

end CutWordArea

namespace CutBoundaryWord.AreaSample

open Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord (AreaSample)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {primitive : Fin source → Stokes.PrimitivePoint} {anchor : Fin
    source}

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- Each cached step comes from an entry in the original boundary alphabet. -/
theorem step_entry_mem (sample : CutBoundaryWord.AreaSample word primitive (primitive anchor))
    {step : CutWordArea.Step (labels := labels) (generators := word.alphabet.generators) primitive sample.values}
    (member : step ∈ sample.steps) : step.entry ∈ word.alphabet.entries := by
  rw [← CutWordArea.steps_entries primitive sample.values word.alphabet.entries (primitive anchor), ← sample.steps_eq]
  exact Map.mem_map_of_mem member

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
open Purelib.Topology.Surface.Cut.WordAreaBounds in
/-- Every cached step drift obeys the complete closed-boundary length bound.

The cached step equation retains its original boundary-entry occurrence. The edge readback equation identifies that same
list length, preserving the modeled drift and both count factors. -/
theorem step_drift_bounded (sample : CutBoundaryWord.AreaSample word primitive (primitive anchor))
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    {bound : PrimitiveAreaBounds.AreaCoordinate} (nonnegative : 0 ≤ bound)
    (bounded : CutWordArea.ErrorsBounded primitive sample.values word.alphabet.entries bound)
    (step : CutWordArea.Step (labels := labels) (generators := word.alphabet.generators) primitive sample.values)
    (member : step ∈ sample.steps) :
    (PrimitivePoint.Bounded step.drift) ((edges.length : PrimitiveAreaBounds.AreaCoordinate) * ((edges.length :
      PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  rw [sample.steps_eq] at member
  have estimate := CutWordArea.steps_drifts_bounded bounded nonnegative
    (by rw [word.alphabet.edges_eq]; exact closed) step member
  have lengthEq := congrArg List.length word.alphabet.edges_eq
  rw [Map.length_map] at lengthEq
  rw [lengthEq] at estimate
  exact estimate

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
open Purelib.Topology.Surface.Cut.WordAreaBounds in
open Purelib.Topology.Surface.Cut.WordAreaBounds.CutBoundaryWord in
open Purelib.Topology.Surface.Cut.WordAreaBounds.CutWordArea in
/-- All cached step corrections satisfy the requested full boundary-area error bound.

The closed boundary supplies the retained prefix paths and endpoint bounds. Weighted allocation pays each original step
correction using the actual complete step count, without discarding local drift or increment-error terms. -/
theorem correction_accurate (sample : CutBoundaryWord.AreaSample word primitive (primitive anchor))
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    {target magnitude : PrimitiveAreaBounds.AreaCoordinate} (positive : 0 < target) (nonnegative : 0 ≤ magnitude)
    (bounded : CutWordArea.ErrorsBounded primitive sample.values word.alphabet.entries
      (Aggregate.perTerm (Weighted.allowance target (CutWordArea.areaWeight magnitude edges.length)) edges.length))
    (increments : ∀ entry ∈ word.alphabet.entries,
      (PrimitivePoint.Bounded (Pairing.linear entry.letter.coefficients sample.values)) (4 * magnitude))
    (endpoints : ∀ entry ∈ word.alphabet.entries, (PrimitivePoint.Bounded (primitive entry.edge.start)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq sample.correction < target := by
  have localPositive := Aggregate.perTerm_positive
    (Weighted.allowance_positive positive (CutWordArea.areaWeight_nonnegative nonnegative edges.length)) edges.length
  have lengthEq : sample.steps.length = edges.length := by
    rw [sample.steps_eq, CutWordArea.steps_length]
    have equal := congrArg List.length word.alphabet.edges_eq
    rw [Map.length_map] at equal
    exact equal
  rw [sample.correction_eq, CutWordArea.correction_eq_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro value member
  obtain ⟨step, member, same⟩ := Map.mem_map.mp member
  rw [← same, Map.length_map, lengthEq]
  have entryMember := step_entry_mem sample member
  have estimate := Step.correction_bounded step edges.length
    (step_drift_bounded sample closed localPositive.le bounded step member)
    (by rw [step.increment_eq]; exact increments step.entry entryMember)
    (endpoints step.entry entryMember)
    (by rw [step.error_eq, step.increment_eq]; exact bounded step.entry entryMember)
  exact estimate.trans (WeightedAggregateBudget.weighted_perTerm_le positive
    (CutWordArea.areaWeight_nonnegative nonnegative edges.length) edges.length)

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- Centering the retained anchor at zero makes the closed correction equal the full step correction.

The cached closed-correction equation subtracts the anchor pairing with its retained total error. Scalar transport of
the supplied centered anchor makes that pairing zero while keeping the dependent sample and all its caches unchanged. -/
theorem closedCorrection_eq_of_centered (sample : CutBoundaryWord.AreaSample word primitive (primitive anchor))
    (centered : primitive anchor = PrimitivePoint.zero) : sample.closedCorrection = sample.correction := by
  rw [sample.closedCorrection_eq]
  have areaZero : Stokes.edgeArea (primitive anchor) sample.errorTotal = 0 := by
    refine (congrArg (fun point => Stokes.edgeArea point sample.errorTotal) centered).trans ?_
    change 0 * sample.errorTotal.right - sample.errorTotal.left * 0 = 0
    rw [Gaussian.Basic.zero_mul, Gaussian.Basic.mul_zero, Gaussian.Basic.sub_zero]
  rw [areaZero, Gaussian.Basic.sub_zero]

end CutBoundaryWord.AreaSample
end Purelib.Topology.Surface.Cut.WordAreaBounds
