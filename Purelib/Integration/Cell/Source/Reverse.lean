module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Partition.Unit.Reverse
public import Purelib.Approximation.Rational.Uniform.Reverse
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Reflecting an original source frontier

Every original cell and cached source reading is retained at its reflected
point, in reversed partition order. The range and exact weight are unchanged,
so the two finite integral enclosures are identical.
-/

public section

namespace Purelib.Integration.SourceFrontier.Reverse

open Purelib.Approximation.Rational
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Reflect an original tagged source point while retaining its actual cached reading. -/
@[expose] def point {source : Fraction.Rational → Fraction.Rational}
    (tag : SourcePoint source) : SourcePoint (Uniform.reversed source) where
  interval := Unit.Reverse.interval tag.interval
  point := Unit.Reverse.point tag.point
  start_le := Fraction.Order.Arithmetic.sub_le_sub_left_direct tag.point_le_finish 1
  point_le_finish := Fraction.Order.Arithmetic.sub_le_sub_left_direct tag.start_le 1
  reading := tag.reading
  reading_eq := by
    change tag.reading = source (Unit.Reverse.point (Unit.Reverse.point tag.point))
    rw [Unit.Reverse.point_point, tag.reading_eq]

/-- Reflect one original cell, preserving its exact weight and range. -/
@[expose] def cell {source : Fraction.Rational → Fraction.Rational}
    (original : IntegrationCell (SourcePoint source)) : IntegrationCell (SourcePoint (Uniform.reversed source)) where
  item := point original.item
  weight := original.weight
  weight_nonnegative := original.weight_nonnegative
  lower := original.lower
  upper := original.upper
  range_valid := original.range_valid

/-- Reflect an actual source frontier, keeping its original cells and cached readings in reverse order. -/
@[expose] def frontier {source : Fraction.Rational → Fraction.Rational}
    (original : SourceFrontier source) : SourceFrontier (Uniform.reversed source) where
  partition := Unit.Reverse.partition original.partition
  cells := original.cells.reverse.map cell
  domains_eq := by
    have domains : (original.cells.reverse.map (fun old => old.item.interval)) = original.partition.intervals.reverse :=
      (Reverse.map_reverse _ original.cells).trans (congrArg List.reverse original.domains_eq)
    change ((original.cells.reverse.map cell).map (fun current => current.item.interval)) =
      original.partition.intervals.reverse.map Unit.Reverse.interval
    rw [Map.map_map, ← domains, Map.map_map]
    rfl
  weight_eq := by
    intro current member
    obtain ⟨old, oldMember, equal⟩ := Map.mem_map.mp member
    have originalMember := (Reverse.mem_reverse original.cells).mp oldMember
    rw [← equal]
    change old.weight = (Unit.Reverse.interval old.item.interval).signedLength
    rw [Unit.Reverse.interval_length]
    exact original.weight_eq old originalMember
  source_range := by
    intro current member query lower upper
    obtain ⟨old, oldMember, equal⟩ := Map.mem_map.mp member
    have originalMember := (Reverse.mem_reverse original.cells).mp oldMember
    rw [← equal] at lower upper ⊢
    change Unit.Reverse.point old.item.interval.finish ≤ query at lower
    change query ≤ Unit.Reverse.point old.item.interval.start at upper
    have first := Fraction.Order.Arithmetic.sub_le_sub_left_direct upper 1
    have second := Fraction.Order.Arithmetic.sub_le_sub_left_direct lower 1
    change Unit.Reverse.point (Unit.Reverse.point old.item.interval.start) ≤ Unit.Reverse.point query at first
    change Unit.Reverse.point query ≤ Unit.Reverse.point (Unit.Reverse.point old.item.interval.finish) at second
    rw [Unit.Reverse.point_point] at first second
    exact original.source_range old originalMember (Unit.Reverse.point query) first second

/-- Reflecting and reversing cells preserves the original lower integral sum. -/
theorem lowerIntegral_reverse {source : Fraction.Rational → Fraction.Rational} :
    ∀ cells : List (IntegrationCell (SourcePoint source)), lowerIntegral (cells.reverse.map cell) = lowerIntegral cells
  | [] => rfl
  | first :: remaining => by
      rw [Reverse.reverse_cons, Map.map_append, lowerIntegral_append, lowerIntegral_reverse remaining]
      change lowerIntegral remaining + (first.weight * first.lower + 0) =
        first.weight * first.lower + lowerIntegral remaining
      ring1

/-- Reflecting and reversing cells preserves the original upper integral sum. -/
theorem upperIntegral_reverse {source : Fraction.Rational → Fraction.Rational} :
    ∀ cells : List (IntegrationCell (SourcePoint source)), upperIntegral (cells.reverse.map cell) = upperIntegral cells
  | [] => rfl
  | first :: remaining => by
      rw [Reverse.reverse_cons, Map.map_append, upperIntegral_append, upperIntegral_reverse remaining]
      change upperIntegral remaining + (first.weight * first.upper + 0) =
        first.weight * first.upper + upperIntegral remaining
      ring1

/-- The reflected and original frontiers have exactly the same rational integral enclosure. -/
theorem integralBound_eq {source : Fraction.Rational → Fraction.Rational} (original : SourceFrontier source) :
    integralBound (frontier original).cells = integralBound original.cells := by
  apply Purelib.Data.Rat.Interval.ext
  · exact lowerIntegral_reverse original.cells
  · exact upperIntegral_reverse original.cells

end Purelib.Integration.SourceFrontier.Reverse

end
