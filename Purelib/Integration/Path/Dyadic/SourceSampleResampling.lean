module
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Polynomial.Rectangle.SampleReadback
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Mesh-width resampling estimates for the actual cached centered samples.
Reflecting parameters preserves every sample field by pointwise readback. -/
namespace Purelib.Integration.Path.Dyadic.SourceSampleResampling

open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
open Purelib.Data.Gaussian
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon
open Purelib.Integration.Polynomial.Rectangle

open Purelib.Data.List

open Purelib.Integration.Path.Dyadic.SourceResampling

/-- The rational carrier for oriented source parameters and mesh-width bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Rat.Fraction.Compatibility

/-- Read the exact directed parameter difference in the supplied orientation. -/
@[expose] def parameterStep (forward : Bool) (first last : Coordinate) : Coordinate :=
  if forward then last - first else first - last

/-- The maximum of zero and the original retained rational list entries. -/
@[expose] def maximum : List Coordinate → Coordinate
  | [] => 0
  | value :: rest => max value (Purelib.Integration.Path.Dyadic.SourceSampleResampling.maximum rest)

/-- Every original list entry is bounded by its retained zero-based maximum. -/
theorem le_maximum {values : List Coordinate} {value : Coordinate}
    (member : value ∈ values) : value ≤ SourceSampleResampling.maximum values := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases Membership.mem_cons.mp member with rfl | present
    · exact Fraction.Order.Basic.le_max_left _ _
    · exact (ih present).trans (Fraction.Order.Basic.le_max_right _ _)

/-- A common nonnegative entry bound bounds the original list's zero-based maximum. -/
private theorem maximum_le {values : List Coordinate} {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, value ≤ bound) : SourceSampleResampling.maximum values ≤
      bound := by
  induction values with
  | nil => exact nonnegative
  | cons head tail ih =>
    exact Fraction.Order.Basic.max_le (bounded head (List.mem_cons_self ..))
      (ih (fun value member => bounded value (List.mem_cons_of_mem head member)))

/-- The original list's zero-based maximum is nonnegative. -/
private theorem maximum_nonnegative (values : List Coordinate) : 0 ≤ SourceSampleResampling.maximum values := by
  induction values with
  | nil => exact le_rfl
  | cons head tail ih => exact ih.trans (Fraction.Order.Basic.le_max_right _ _)

/-- Read the zero-based maximum of the original indexed parameter steps in the supplied orientation.

The finite table contains the original oriented step for every bounded edge index. Its maximum includes zero and does
not reorder or replace those steps. -/
@[expose] def meshWidth {count : Nat} (parameters : Fin (count + 1) → Coordinate) (forward : Bool) : Coordinate :=
  SourceSampleResampling.maximum (List.ofFn (fun edge : Fin count => SourceSampleResampling.parameterStep forward
    (parameters edge.castSucc) (parameters edge.succ)))

/-- The retained oriented mesh width is nonnegative. -/
theorem meshWidth_nonnegative {count : Nat} (parameters : Fin (count + 1) → Coordinate) (forward : Bool) :
    0 ≤ SourceSampleResampling.meshWidth parameters forward := SourceSampleResampling.maximum_nonnegative _

/-- Every exact original oriented parameter step is bounded by the retained mesh width.

The displayed edge index witnesses occurrence in the original finite table. Its oriented parameter step is compared with
the maximum of that same table. -/
theorem step_le_meshWidth {count : Nat} (parameters : Fin (count + 1) → Coordinate) (forward : Bool)
    (edge : Fin count) : SourceSampleResampling.parameterStep forward (parameters edge.castSucc) (parameters edge.succ)
      ≤ SourceSampleResampling.meshWidth parameters forward :=
  SourceSampleResampling.le_maximum (OfFn.Basic.mem_ofFn.mpr ⟨edge, rfl⟩)

/-- A common nonnegative bound on original oriented steps bounds the retained mesh width.

Every original finite-table occurrence has its retained edge index. The common bound applies to those same displayed
steps and to the zero base case. -/
theorem meshWidth_le {count : Nat} (parameters : Fin (count + 1) → Coordinate) (forward : Bool)
    {bound : Coordinate} (nonnegative : 0 ≤ bound)
    (bounded : ∀ edge : Fin count, SourceSampleResampling.parameterStep forward (parameters edge.castSucc) (parameters
      edge.succ) ≤ bound) :
    SourceSampleResampling.meshWidth parameters forward ≤ bound := by
  apply SourceSampleResampling.maximum_le nonnegative
  intro value member
  obtain ⟨edge, rfl⟩ := OfFn.Basic.mem_ofFn.mp member
  exact bounded edge

/-- Two retained increasing samples with common endpoints satisfy the source resampling area bound.

Both original parameter families have bounded steps in the unit interval, and their separate sample caches keep the same
endpoint correction. -/
private theorem increasing_sample_bound (values : Coordinate → Stokes.PrimitivePoint) {density width : Coordinate}
    (increment : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (values b) (values a))
        (density * (b - a) ^ 2))
    {count nextCount : Nat} (parameters : Fin (count + 1) → Coordinate) (next : Fin (nextCount + 1) → Coordinate)
    (ordered : ∀ edge : Fin count, parameters edge.castSucc ≤ parameters edge.succ)
    (nextOrdered : ∀ edge : Fin nextCount, next edge.castSucc ≤ next edge.succ)
    (lower : 0 ≤ parameters 0) (upper : parameters (Fin.last count) ≤ 1)
    (first_eq : parameters 0 = next 0) (last_eq : parameters (Fin.last count) = next (Fin.last nextCount))
    (steps : ∀ edge : Fin count, parameters edge.succ - parameters edge.castSucc ≤ width)
    (nextSteps : ∀ edge : Fin nextCount, next edge.succ - next edge.castSucc ≤ width)
    (source : CenteredBilinearPath.Sample (fun vertex => values (parameters vertex)))
    (resampled : CenteredBilinearPath.Sample (fun vertex => values (next vertex))) :
    Data.Gaussian.Norm.Basic.normSq (source.centeredArea - resampled.centeredArea) ≤
      16 * density ^ 2 * width ^ 2 * (parameters (Fin.last count) - parameters 0) ^ 2 := by
  have nextChain : SourceResampling.Chain (parameters 0) (List.ofFn (fun edge : Fin nextCount => next edge.succ))
      (parameters (Fin.last count)) := by
    rw [first_eq, last_eq]
    exact SourceResampling.chain_ofFn next nextOrdered
  have nextWidths : SourceResampling.widths (parameters 0) (List.ofFn (fun edge : Fin nextCount => next edge.succ))
    width := by
    rw [first_eq]
    exact SourceResampling.widths_ofFn next width nextSteps
  have bound := SourceResampling.resampling_bound values increment (SourceResampling.chain_ofFn parameters ordered)
    nextChain lower upper
    (SourceResampling.widths_ofFn parameters width steps) nextWidths
  have rightArea := (congrArg (fun first => SourceResampling.rawArea values first
    (List.ofFn (fun edge : Fin nextCount => next edge.succ))) first_eq).trans (SourceResampling.rawArea_ofFn values
      next)
  have uncentered := (congrArg₂ (fun left right => Data.Gaussian.Norm.Basic.normSq (left - right))
    (SourceResampling.rawArea_ofFn values parameters) rightArea).symm.trans_le bound
  have endpoints : source.endpoint = resampled.endpoint := by
    rw [source.endpoint_eq, resampled.endpoint_eq, first_eq, last_eq]
  have equal : source.centeredArea - resampled.centeredArea =
      CenteredBilinearPath.area (fun vertex => values (parameters vertex)) -
        CenteredBilinearPath.area (fun vertex => values (next vertex)) := by
    rw [← source.originalArea_eq, ← resampled.originalArea_eq, source.decomposition, resampled.decomposition, endpoints]
    ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_le uncentered

/-- Reflect the exact rational parameter about the midpoint of the unit interval. -/
private def reflect (parameter : Coordinate) : Coordinate := 1 - parameter

/-- Reflecting the original rational parameter twice returns that parameter. -/
private theorem reflect_twice (parameter : Coordinate) : SourceSampleResampling.reflect (SourceSampleResampling.reflect
  parameter) = parameter := by
  dsimp only [SourceSampleResampling.reflect]
  ring1

/-- Reflection preserves membership in the exact unit interval. -/
private theorem reflect_unit {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    0 ≤ SourceSampleResampling.reflect parameter ∧ SourceSampleResampling.reflect parameter ≤ 1 :=
  ⟨Fraction.Order.Arithmetic.sub_nonneg_direct inside.2, (Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl
    inside.1).trans_eq (by ring1)⟩

/-- Compare retained source samples in either common orientation with their original shared endpoints and width bounds.

The original parameter families and sample owners remain separate; decreasing families are transported through unit
reflection without changing their cached centered areas. -/
theorem sample_bound (values : Coordinate → Stokes.PrimitivePoint) {density width : Coordinate}
    (increment : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (values b) (values a))
        (density * (b - a) ^ 2))
    {count nextCount : Nat} (parameters : Fin (count + 1) → Coordinate) (next : Fin (nextCount + 1) → Coordinate)
    (inside : ∀ vertex, 0 ≤ parameters vertex ∧ parameters vertex ≤ 1)
    (nextInside : ∀ vertex, 0 ≤ next vertex ∧ next vertex ≤ 1)
    (forward : Bool)
    (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (nextOrdered : ∀ edge : Fin nextCount, if forward then next edge.castSucc ≤ next edge.succ
      else next edge.succ ≤ next edge.castSucc)
    (first_eq : parameters 0 = next 0) (last_eq : parameters (Fin.last count) = next (Fin.last nextCount))
    (steps : ∀ edge : Fin count, SourceSampleResampling.parameterStep forward (parameters edge.castSucc) (parameters
      edge.succ) ≤ width)
    (nextSteps : ∀ edge : Fin nextCount, SourceSampleResampling.parameterStep forward (next edge.castSucc) (next
      edge.succ) ≤ width)
    (source : CenteredBilinearPath.Sample (fun vertex => values (parameters vertex)))
    (resampled : CenteredBilinearPath.Sample (fun vertex => values (next vertex))) :
    Data.Gaussian.Norm.Basic.normSq (source.centeredArea - resampled.centeredArea) ≤
      16 * density ^ 2 * width ^ 2 * (parameters (Fin.last count) - parameters 0) ^ 2 := by
  cases forward with
  | true =>
    exact SourceSampleResampling.increasing_sample_bound values increment parameters next ordered nextOrdered
      ((nextInside 0).1.trans_eq first_eq.symm) (inside (Fin.last count)).2 first_eq last_eq steps nextSteps source
        resampled
  | false =>
    let reflected := fun parameter => values (SourceSampleResampling.reflect parameter)
    have reflectedIncrement (a b : Coordinate) (al : 0 ≤ a) (au : a ≤ 1) (bl : 0 ≤ b) (bu : b ≤ 1) :
        PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (reflected b) (reflected a))
          (density * (b - a) ^ 2) := by
      have aInside := SourceSampleResampling.reflect_unit ⟨al, au⟩
      have bInside := SourceSampleResampling.reflect_unit ⟨bl, bu⟩
      have original := increment (SourceSampleResampling.reflect a) (SourceSampleResampling.reflect b) aInside.1
        aInside.2 bInside.1 bInside.2
      have scalar : density * (SourceSampleResampling.reflect b - SourceSampleResampling.reflect a) ^ 2 = density * (b -
        a) ^ 2 := by dsimp only [SourceSampleResampling.reflect]; ring1
      exact ⟨original.1.trans_eq scalar, original.2.trans_eq scalar⟩
    let left := SampleReadback.Sample.readback source
      (last := fun vertex => reflected (SourceSampleResampling.reflect (parameters vertex)))
      (fun vertex => (congrArg values (SourceSampleResampling.reflect_twice (parameters vertex))).symm)
    let right := SampleReadback.Sample.readback resampled
      (last := fun vertex => reflected (SourceSampleResampling.reflect (next vertex)))
      (fun vertex => (congrArg values (SourceSampleResampling.reflect_twice (next vertex))).symm)
    have bound := SourceSampleResampling.increasing_sample_bound reflected reflectedIncrement
      (fun vertex => SourceSampleResampling.reflect (parameters vertex)) (fun vertex => SourceSampleResampling.reflect
        (next vertex))
      (fun edge => Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl (ordered edge))
      (fun edge => Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl (nextOrdered edge))
      ((SourceSampleResampling.reflect_unit (nextInside 0)).1.trans_eq (congrArg SourceSampleResampling.reflect
        first_eq.symm)) (SourceSampleResampling.reflect_unit (inside (Fin.last count))).2
      (congrArg SourceSampleResampling.reflect first_eq) (congrArg SourceSampleResampling.reflect last_eq)
      (fun edge => (show SourceSampleResampling.reflect (parameters edge.succ) - SourceSampleResampling.reflect
        (parameters edge.castSucc) =
        parameters edge.castSucc - parameters edge.succ by dsimp only [SourceSampleResampling.reflect]; ring1).trans_le
          (steps edge))
      (fun edge => (show SourceSampleResampling.reflect (next edge.succ) - SourceSampleResampling.reflect (next
        edge.castSucc) =
        next edge.castSucc - next edge.succ by dsimp only [SourceSampleResampling.reflect]; ring1).trans_le (nextSteps
          edge)) left right
    exact bound.trans_eq (by dsimp only [SourceSampleResampling.reflect]; ring1)

end Purelib.Integration.Path.Dyadic.SourceSampleResampling

end
