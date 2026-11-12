module
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Partition.Exceptional.Region
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Replacing a rational source on finite regions

The original partition, ordered cell occurrences, and unmarked cached readings
are retained. A global range covers cells meeting any closed exceptional region.
-/

public section

namespace Purelib.Integration.SourceFrontier.Exceptional.Region

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.List.Rat.Linear
open Purelib.Integration.Partition

/-- A false Boolean test cannot also be true. -/
private theorem not_true_of_false {test : Bool} (rejected : test = false) : ¬ test = true := by
  intro accepted
  rw [rejected] at accepted
  cases accepted

/-- The point belongs to none of the retained closed regions. -/
def Outside (regions : List Partition.Interval) (point : Fraction.Rational) : Prop :=
  ∀ region ∈ regions, ¬ (region.start ≤ point ∧ point ≤ region.finish)

/-- Every point of an unmarked cell lies outside each retained region. -/
theorem outside_of_unmarked (interval : Partition.Interval) (regions : List Partition.Interval)
    (unmarked : interval.regionMarked regions = false) (point : Fraction.Rational)
    (lower : interval.start ≤ point) (upper : point ≤ interval.finish) : Outside regions point := by
  intro region member inside
  have marked := interval.regionMarked_of_point regions region member point lower upper inside.1 inside.2
  rw [unmarked] at marked
  cases marked

/-- Retain the original tag and reuse its cached reading on cells outside all regions. -/
@[expose] def point {original target : Fraction.Rational → Fraction.Rational}
    (regions : List Partition.Interval) (agreement : ∀ point, Outside regions point → target point = original point)
    (tag : SourcePoint original) : SourcePoint target where
  interval := tag.interval
  point := tag.point
  start_le := tag.start_le
  point_le_finish := tag.point_le_finish
  reading := if tag.interval.regionMarked regions then target tag.point else tag.reading
  reading_eq := by
    cases marked : tag.interval.regionMarked regions with
    | true => rfl
    | false =>
        change tag.reading = target tag.point
        rw [tag.reading_eq]
        exact (agreement tag.point (outside_of_unmarked tag.interval regions marked tag.point
          tag.start_le tag.point_le_finish)).symm

/-- Replace one source cell, widening its range only when it meets a retained region. -/
@[expose] def cell {original target : Fraction.Rational → Fraction.Rational}
    (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) : IntegrationCell (SourcePoint target) where
  item := point regions agreement retained.item
  weight := retained.weight
  weight_nonnegative := retained.weight_nonnegative
  lower := if retained.item.interval.regionMarked regions then global.lower else retained.lower
  upper := if retained.item.interval.regionMarked regions then global.upper else retained.upper
  range_valid := by
    cases marked : retained.item.interval.regionMarked regions with
    | true => exact global.valid
    | false => exact retained.range_valid

/-- An unmarked cell retains its exact original cached reading. -/
theorem cell_reading_of_unmarked {original target : Fraction.Rational → Fraction.Rational}
    (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (retained : IntegrationCell (SourcePoint original))
    (unmarked : retained.item.interval.regionMarked regions = false) :
    (cell regions global agreement retained).item.reading = retained.item.reading := by
  change (if retained.item.interval.regionMarked regions then target retained.item.point else retained.item.reading) = _
  rw [if_neg (not_true_of_false unmarked)]

/-- Transport a retained source frontier through equality outside the finite closed regions.

The same partition, cell order, weights and tags are retained. The supplied
global range covers target readings on the unit interval; unmarked cells keep
their original source range and cached reading. -/
@[expose] def replace {original target : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) : SourceFrontier target where
  partition := retained.partition
  cells := retained.cells.map (cell regions global agreement)
  domains_eq := by
    rw [Purelib.Data.List.Map.map_map]
    exact retained.domains_eq
  weight_eq := by
    intro replacement member
    obtain ⟨originalCell, originalMember, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
    rw [← equal]
    exact retained.weight_eq originalCell originalMember
  source_range := by
    intro replacement member query lower upper
    obtain ⟨originalCell, originalMember, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
    rw [← equal] at lower upper ⊢
    have domainMember : originalCell.item.interval ∈ retained.partition.intervals := by
      rw [← retained.domains_eq]
      exact Purelib.Data.List.Map.mem_map_of_mem originalMember
    have valid := retained.partition.valid originalCell.item.interval domainMember
    cases marked : originalCell.item.interval.regionMarked regions with
    | true =>
        change (if originalCell.item.interval.regionMarked regions then global.lower else originalCell.lower) ≤
          target query ∧ target query ≤
            (if originalCell.item.interval.regionMarked regions then global.upper else originalCell.upper)
        rw [if_pos marked, if_pos marked]
        exact bounded query (valid.1.trans lower) (upper.trans valid.2.2)
    | false =>
        change (if originalCell.item.interval.regionMarked regions then global.lower else originalCell.lower) ≤
          target query ∧ target query ≤
            (if originalCell.item.interval.regionMarked regions then global.upper else originalCell.upper)
        rw [if_neg (not_true_of_false marked), if_neg (not_true_of_false marked)]
        rw [agreement query (outside_of_unmarked originalCell.item.interval regions marked query lower upper)]
        exact retained.source_range originalCell originalMember query lower upper

/-- A marked cell adds at most the global range width to the original cell oscillation. -/
private theorem cell_oscillation_le {original target : Fraction.Rational → Fraction.Rational}
    (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) :
    (cell regions global agreement retained).oscillation ≤ retained.oscillation +
      (if retained.item.interval.regionMarked regions then global.width else 0) := by
  cases marked : retained.item.interval.regionMarked regions with
  | true =>
      change (if retained.item.interval.regionMarked regions then global.upper else retained.upper) -
        (if retained.item.interval.regionMarked regions then global.lower else retained.lower) ≤ _
      rw [if_pos marked, if_pos marked]
      change global.width ≤ retained.oscillation + global.width
      have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct retained.oscillation_nonneg global.width
      rw [Fraction.Field.zero_add] at shifted
      exact shifted
  | false =>
      change (if retained.item.interval.regionMarked regions then global.upper else retained.upper) -
        (if retained.item.interval.regionMarked regions then global.lower else retained.lower) ≤ _
      rw [if_neg (not_true_of_false marked), if_neg (not_true_of_false marked)]
      change retained.oscillation ≤ retained.oscillation + 0
      have identity : retained.oscillation + 0 = retained.oscillation := by ring1
      rewrite [identity]
      exact Fraction.Order.Basic.le_refl _

/-- The original marked cell weights are exactly the partition's union length. -/
private theorem regions_weight_eq {original : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (regions : List Partition.Interval) :
    (retained.cells.map (fun cell => if cell.item.interval.regionMarked regions then cell.weight else 0)).sum =
      retained.partition.regionsLength regions := by
  have weights : ∀ cell ∈ retained.cells,
      (if cell.item.interval.regionMarked regions then cell.weight else 0) =
        if cell.item.interval.regionMarked regions then cell.item.interval.signedLength else 0 := by
    intro cell member
    rw [retained.weight_eq cell member]
  calc
    _ = (retained.cells.map (fun cell =>
        if cell.item.interval.regionMarked regions then cell.item.interval.signedLength else 0)).sum :=
      sum_congr _ _ retained.cells weights
    _ = ((retained.cells.map (fun cell => cell.item.interval)).map
        (fun interval => if interval.regionMarked regions then interval.signedLength else 0)).sum := by
      rw [Purelib.Data.List.Map.map_map]
      rfl
    _ = retained.partition.regionsLength regions := by rw [retained.domains_eq]; rfl

/-- Replacement costs at most the global width times the actual union of marked cell lengths.

Overlapping regions and shared endpoints charge each retained cell once;
the original weighted oscillation and every unmarked range remain in the result. -/
theorem replace_oscillation_le {original target : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    integralOscillation (replace retained regions global agreement bounded).cells ≤
      integralOscillation retained.cells + retained.partition.regionsLength regions * global.width := by
  let replacement := cell regions global agreement
  let markedWeight := fun retainedCell : IntegrationCell (SourcePoint original) =>
    if retainedCell.item.interval.regionMarked regions then retainedCell.weight else 0
  have weighted : ∀ retainedCell ∈ retained.cells,
      (replacement retainedCell).weight * (replacement retainedCell).oscillation ≤
        retainedCell.weight * retainedCell.oscillation + markedWeight retainedCell * global.width := by
    intro retainedCell _
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (cell_oscillation_le regions global agreement retainedCell) retainedCell.weight_nonnegative
    change retainedCell.weight * (replacement retainedCell).oscillation ≤ _ at scaled
    cases marked : retainedCell.item.interval.regionMarked regions with
    | false =>
        rw [if_neg (not_true_of_false marked)] at scaled
        dsimp only [markedWeight]
        rw [if_neg (not_true_of_false marked)]
        have identity : retainedCell.weight * (retainedCell.oscillation + 0) =
            retainedCell.weight * retainedCell.oscillation + 0 * global.width := by ring1
        rw [identity] at scaled
        exact scaled
    | true =>
        rw [if_pos marked] at scaled
        dsimp only [markedWeight]
        rw [if_pos marked]
        have identity : retainedCell.weight * (retainedCell.oscillation + global.width) =
            retainedCell.weight * retainedCell.oscillation + retainedCell.weight * global.width := by ring1
        rw [identity] at scaled
        exact scaled
  calc
    integralOscillation (replace retained regions global agreement bounded).cells =
        (retained.cells.map (fun retainedCell =>
          (replacement retainedCell).weight * (replacement retainedCell).oscillation)).sum := by
      rw [integralOscillation_eq_sum]
      change ((retained.cells.map replacement).map (fun other => other.weight * other.oscillation)).sum = _
      rw [Purelib.Data.List.Map.map_map]
      rfl
    _ ≤ (retained.cells.map (fun retainedCell => retainedCell.weight * retainedCell.oscillation +
        markedWeight retainedCell * global.width)).sum := sum_le _ _ retained.cells weighted
    _ = integralOscillation retained.cells + retained.partition.regionsLength regions * global.width := by
      rw [sum_add, sum_mul_right, ← integralOscillation_eq_sum, regions_weight_eq]

/-- The replacement enclosure width is bounded by the original width and actual marked-cell contribution. -/
theorem replace_width_le {original target : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    (integralBound (replace retained regions global agreement bounded).cells).width ≤
      (integralBound retained.cells).width + retained.partition.regionsLength regions * global.width := by
  rw [integralBound_width, integralBound_width]
  exact replace_oscillation_le retained regions global agreement bounded

set_option genInjectivity false in
/-- One finite region-replacement attempt with its actual original and replacement frontiers.

The source agreement, global bound, regions and request remain attached to
the same original frontier. The replacement is computed once and retained;
no successful final width is assumed. -/
structure Attempt (original target : Fraction.Rational → Fraction.Rational) where
  /-- The original source-linked frontier and its cached observations. -/ retained : SourceFrontier original
  /-- The original finite exceptional regions. -/ regions : List Partition.Interval
  /-- The supplied target range on marked cells. -/ global : Purelib.Data.Rat.Interval
  /-- The target and original readings agree outside the retained regions. -/ agreement :
    ∀ point, Outside regions point → target point = original point
  /-- The global target range covers all rational unit-interval readings. -/ bounded :
    ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)
  /-- The original positive requested enclosure width. -/ request : AccuracyRequest
  /-- The actual retained replacement and its source-linked cells. -/ frontier : SourceFrontier target
  /-- The retained replacement is the one constructed from the same original inputs. -/ frontier_eq :
    frontier = replace retained regions global agreement bounded

constructive_injectivity Attempt

namespace Attempt

/-- Construct the finite attempt, retaining its computed source-linked replacement. -/
@[expose] def make {original target : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (regions : List Partition.Interval) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, Outside regions point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point))
    (request : AccuracyRequest) : Attempt original target where
  retained := retained
  regions := regions
  global := global
  agreement := agreement
  bounded := bounded
  request := request
  frontier := replace retained regions global agreement bounded
  frontier_eq := rfl

/-- Read the exact weighted exceptional charge from the retained original cells. -/
@[expose] def exceptionalCharge {original target : Fraction.Rational → Fraction.Rational}
    (attempt : Attempt original target) : Fraction.Rational :=
  attempt.retained.partition.regionsLength attempt.regions * attempt.global.width

/-- The computed replacement width is bounded by the original width and retained exceptional charge. -/
theorem width_le {original target : Fraction.Rational → Fraction.Rational} (attempt : Attempt original target) :
    (integralBound attempt.frontier.cells).width ≤
      (integralBound attempt.retained.cells).width + attempt.exceptionalCharge := by
  rw [attempt.frontier_eq]
  exact replace_width_le attempt.retained attempt.regions attempt.global attempt.agreement attempt.bounded

set_option genInjectivity false in
/-- The finite attempt either meets its request or records that this particular computed width does not.

The inconclusive branch retains the same attempted frontier and exact failed
comparison. It states no global failure of integrability. -/
inductive Outcome {original target : Fraction.Rational → Fraction.Rational} (attempt : Attempt original target) where
  /-- The retained replacement meets the original request. -/ | sufficient
      (accurate : (integralBound attempt.frontier.cells).width < attempt.request.tolerance)
  /-- This finite replacement did not meet the request. -/ | inconclusive
      (unpaid : ¬ (integralBound attempt.frontier.cells).width < attempt.request.tolerance)

constructive_injectivity Outcome

/-- Check the exact width of this finite attempt without changing its regions, request or source caches. -/
@[expose] def check {original target : Fraction.Rational → Fraction.Rational} (attempt : Attempt original target) :
    Outcome attempt :=
  if accurate : (integralBound attempt.frontier.cells).width < attempt.request.tolerance then
    .sufficient accurate
  else
    .inconclusive accurate

/-- Separate original and exceptional budgets suffice for the same retained attempt. -/
theorem sufficient_of_budget {original target : Fraction.Rational → Fraction.Rational}
    (attempt : Attempt original target)
    (paid : (integralBound attempt.retained.cells).width + attempt.exceptionalCharge < attempt.request.tolerance) :
    (integralBound attempt.frontier.cells).width < attempt.request.tolerance :=
  attempt.width_le.trans_lt paid

end Attempt

end Purelib.Integration.SourceFrontier.Exceptional.Region

end
