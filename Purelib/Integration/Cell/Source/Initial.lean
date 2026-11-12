module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Partition.Unit.Initial
import Purelib.Data.List.Rat.Linear
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Replacing a rational source on an initial region

The original partition and every ordered cell occurrence are retained. A
global value range covers cells meeting the initial region; elsewhere the
original range and cached reading are reused through actual source equality.
-/

public section

namespace Purelib.Integration.SourceFrontier.Initial

open Purelib.Data.Rat
open Purelib.Data.List.Rat.Linear
open Purelib.Integration.Partition

/-- Retain a source tag, reusing target readings and the original reading above the initial region.

On a cell starting at or before the endpoint, a matching target observation
is used when available. Otherwise the supplied pointwise equality identifies
the original cached reading with the target source at that tag. -/
@[expose] def pointCached {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (agreement : ∀ point, endpoint < point → target point = original point)
    (tag : SourcePoint original) : SourcePoint target where
  interval := tag.interval
  point := tag.point
  start_le := tag.start_le
  point_le_finish := tag.point_le_finish
  reading := if tag.interval.start ≤ endpoint then SourcePoint.readCached target cached tag.point else tag.reading
  reading_eq := by
    by_cases marked : tag.interval.start ≤ endpoint
    · rw [if_pos marked, SourcePoint.readCached_eq]
    · rw [if_neg marked, tag.reading_eq]
      exact (agreement tag.point ((Fraction.Order.Arithmetic.lt_of_not_ge_direct marked).trans_le tag.start_le)).symm

/-- Retain a source tag without an additional bank of target readings. -/
@[expose] def point {original target : Fraction.Rational → Fraction.Rational}
    (endpoint : Fraction.Rational) (agreement : ∀ point, endpoint < point → target point = original point)
    (tag : SourcePoint original) : SourcePoint target :=
  pointCached [] endpoint agreement tag

/-- Target-cache selection preserves the complete original replacement point. -/
theorem pointCached_eq {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target)) (endpoint : Fraction.Rational)
    (agreement : ∀ point, endpoint < point → target point = original point) (tag : SourcePoint original) :
    pointCached cached endpoint agreement tag = point endpoint agreement tag := by
  unfold point pointCached
  simp only [-eq_self, -iff_self, SourcePoint.readCached_eq]
  rfl

/-- Replace an original cell's source and use the global range only on initial-region cells. -/
@[expose] def cellCached {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target))
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) : IntegrationCell (SourcePoint target) where
  item := pointCached cached endpoint agreement retained.item
  weight := retained.weight
  weight_nonnegative := retained.weight_nonnegative
  lower := if retained.item.interval.start ≤ endpoint then global.lower else retained.lower
  upper := if retained.item.interval.start ≤ endpoint then global.upper else retained.upper
  range_valid := by
    by_cases marked : retained.item.interval.start ≤ endpoint
    · rw [if_pos marked, if_pos marked]
      exact global.valid
    · rw [if_neg marked, if_neg marked]
      exact retained.range_valid

/-- Replace an original cell without an additional bank of target readings. -/
@[expose] def cell {original target : Fraction.Rational → Fraction.Rational}
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) : IntegrationCell (SourcePoint target) :=
  cellCached [] endpoint global agreement retained

/-- Target-cache selection preserves the complete original replacement cell. -/
theorem cellCached_eq {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target)) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) :
    cellCached cached endpoint global agreement retained = cell endpoint global agreement retained := by
  unfold cell cellCached
  simp only [-eq_self, -iff_self, pointCached_eq]
  rfl

/-- A cell wholly above the endpoint retains its exact original cached tag reading. -/
theorem cell_reading_of_above {original target : Fraction.Rational → Fraction.Rational}
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) (above : endpoint < retained.item.interval.start) :
    (cell endpoint global agreement retained).item.reading = retained.item.reading := by
  change (if retained.item.interval.start ≤ endpoint then target retained.item.point else retained.item.reading) = _
  rw [if_neg above.2]

/-- Transport an original source frontier through equality above an initial region.

The exact original partition, ordered cell weights and tags are preserved.
The supplied global range encloses every target reading on the unit interval;
outside the initial region the original source ranges are retained. -/
@[expose] def replaceCached {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target))
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) : SourceFrontier target where
  partition := retained.partition
  cells := retained.cells.map (cellCached cached endpoint global agreement)
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
    by_cases marked : originalCell.item.interval.start ≤ endpoint
    · change (if originalCell.item.interval.start ≤ endpoint then global.lower else originalCell.lower) ≤ target query ∧
        target query ≤ (if originalCell.item.interval.start ≤ endpoint then global.upper else originalCell.upper)
      rw [if_pos marked, if_pos marked]
      exact bounded query (valid.1.trans lower) (upper.trans valid.2.2)
    · change (if originalCell.item.interval.start ≤ endpoint then global.lower else originalCell.lower) ≤ target query ∧
        target query ≤ (if originalCell.item.interval.start ≤ endpoint then global.upper else originalCell.upper)
      rw [if_neg marked, if_neg marked]
      have above := (Fraction.Order.Arithmetic.lt_of_not_ge_direct marked).trans_le lower
      rw [agreement query above]
      exact retained.source_range originalCell originalMember query lower upper

/-- Replace a frontier without an additional bank of target readings. -/
@[expose] def replace {original target : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) : SourceFrontier target :=
  replaceCached [] retained endpoint global agreement bounded

/-- Target-cache selection preserves the complete original replacement frontier. -/
theorem replaceCached_eq {original target : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint target)) (retained : SourceFrontier original)
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    replaceCached cached retained endpoint global agreement bounded =
      replace retained endpoint global agreement bounded := by
  refine SourceFrontier.ext _ _ ?_ ?_
  · rfl
  · change retained.cells.map (cellCached cached endpoint global agreement) =
      retained.cells.map (cell endpoint global agreement)
    apply Purelib.Data.List.Map.map_congr_left
    intro originalCell _
    exact cellCached_eq cached endpoint global agreement originalCell

/-- Replacing a cell adds at most the global width when it meets the initial region. -/
private theorem cell_oscillation_le {original target : Fraction.Rational → Fraction.Rational}
    (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (retained : IntegrationCell (SourcePoint original)) :
    (cell endpoint global agreement retained).oscillation ≤ retained.oscillation +
      (if retained.item.interval.start ≤ endpoint then global.width else 0) := by
  by_cases marked : retained.item.interval.start ≤ endpoint
  · change (if retained.item.interval.start ≤ endpoint then global.upper else retained.upper) -
      (if retained.item.interval.start ≤ endpoint then global.lower else retained.lower) ≤ _
    rw [if_pos marked, if_pos marked, if_pos marked]
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct retained.oscillation_nonneg global.width
    rw [Fraction.Field.zero_add] at shifted
    exact shifted
  · change (if retained.item.interval.start ≤ endpoint then global.upper else retained.upper) -
      (if retained.item.interval.start ≤ endpoint then global.lower else retained.lower) ≤ _
    rw [if_neg marked, if_neg marked, if_neg marked]
    have identity : retained.oscillation + 0 = retained.oscillation := by ring1
    rw [identity]
    exact Fraction.Order.Basic.le_refl _

/-- The original marked weights are exactly the partition's initial-region length. -/
private theorem initial_weight_eq {original : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) :
    (retained.cells.map (fun cell => if cell.item.interval.start ≤ endpoint then cell.weight else 0)).sum =
      retained.partition.initialLength endpoint := by
  have weights : ∀ cell ∈ retained.cells,
      (if cell.item.interval.start ≤ endpoint then cell.weight else 0) =
        if cell.item.interval.start ≤ endpoint then cell.item.interval.signedLength else 0 := by
    intro cell member
    rw [retained.weight_eq cell member]
  calc
    _ = (retained.cells.map (fun cell =>
        if cell.item.interval.start ≤ endpoint then cell.item.interval.signedLength else 0)).sum :=
      sum_congr _ _ retained.cells weights
    _ = ((retained.cells.map (fun cell => cell.item.interval)).map
        (fun interval => if interval.start ≤ endpoint then interval.signedLength else 0)).sum := by
      rw [Purelib.Data.List.Map.map_map]
      rfl
    _ = retained.partition.initialLength endpoint := by rw [retained.domains_eq]; rfl

/-- Source replacement costs at most the global width times the actual marked length.

The original weighted oscillation remains in the bound. Each initial-region
cell is charged once by its retained weight; all other cells keep their
original range and contribute no replacement cost. -/
theorem replace_oscillation_le {original target : Fraction.Rational → Fraction.Rational}
    (retained : SourceFrontier original) (endpoint : Fraction.Rational) (global : Purelib.Data.Rat.Interval)
    (agreement : ∀ point, endpoint < point → target point = original point)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → global.Contains (target point)) :
    integralOscillation (replace retained endpoint global agreement bounded).cells ≤
      integralOscillation retained.cells + retained.partition.initialLength endpoint * global.width := by
  let replacement := cell endpoint global agreement
  let markedWeight := fun retainedCell : IntegrationCell (SourcePoint original) =>
    if retainedCell.item.interval.start ≤ endpoint then retainedCell.weight else 0
  have weighted : ∀ retainedCell ∈ retained.cells,
      (replacement retainedCell).weight * (replacement retainedCell).oscillation ≤
        retainedCell.weight * retainedCell.oscillation + markedWeight retainedCell * global.width := by
    intro retainedCell _
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (cell_oscillation_le endpoint global agreement retainedCell) retainedCell.weight_nonnegative
    change retainedCell.weight * (replacement retainedCell).oscillation ≤ _ at scaled
    cases marked : decide (retainedCell.item.interval.start ≤ endpoint) with
    | false =>
        have notMarked : ¬ retainedCell.item.interval.start ≤ endpoint := of_decide_eq_false marked
        rw [if_neg notMarked] at scaled
        dsimp only [markedWeight]
        rw [if_neg notMarked]
        have identity : retainedCell.weight * (retainedCell.oscillation + 0) =
            retainedCell.weight * retainedCell.oscillation + 0 * global.width := by ring1
        rw [identity] at scaled
        exact scaled
    | true =>
        have isMarked : retainedCell.item.interval.start ≤ endpoint := of_decide_eq_true marked
        rw [if_pos isMarked] at scaled
        dsimp only [markedWeight]
        rw [if_pos isMarked]
        have identity : retainedCell.weight * (retainedCell.oscillation + global.width) =
            retainedCell.weight * retainedCell.oscillation + retainedCell.weight * global.width := by ring1
        rw [identity] at scaled
        exact scaled
  calc
    integralOscillation (replace retained endpoint global agreement bounded).cells =
        (retained.cells.map (fun retainedCell =>
          (replacement retainedCell).weight * (replacement retainedCell).oscillation)).sum := by
      rw [integralOscillation_eq_sum]
      change ((retained.cells.map replacement).map (fun other => other.weight * other.oscillation)).sum = _
      rw [Purelib.Data.List.Map.map_map]
      rfl
    _ ≤ (retained.cells.map (fun retainedCell => retainedCell.weight * retainedCell.oscillation +
        markedWeight retainedCell * global.width)).sum := sum_le _ _ retained.cells weighted
    _ = integralOscillation retained.cells + retained.partition.initialLength endpoint * global.width := by
      rw [sum_add, sum_mul_right, ← integralOscillation_eq_sum, initial_weight_eq]

end Purelib.Integration.SourceFrontier.Initial

end
