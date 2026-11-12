module
public import Purelib.Integration.Partition.Unit.Basic
public import Purelib.Integration.Partition.Length
import Purelib.Data.List.Reverse
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Reflection of an original unit partition

Reflect each retained endpoint around one half and reverse the occurrence
order. The original cut chain, interval list and signed cell lengths remain
explicitly related to the resulting normalized unit partition.
-/

public section

namespace Purelib.Integration.Partition.Unit.Reverse

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Reflect a rational unit parameter around one half. -/
@[expose] def point (parameter : Fraction.Rational) : Fraction.Rational := 1 - parameter

/-- Reflect an ordered interval and reverse its two endpoint positions. -/
@[expose] def interval (original : Partition.Interval) : Partition.Interval :=
  ⟨point original.finish, point original.start⟩

/-- Reflection preserves the original signed interval length. -/
theorem interval_length (original : Partition.Interval) :
    (interval original).signedLength = original.signedLength := by
  unfold interval point Partition.Interval.signedLength
  ring1

/-- A reflected rational point is restored by a second reflection. -/
theorem point_point (parameter : Fraction.Rational) : point (point parameter) = parameter := by
  unfold point
  ring1

/-- Reflecting two ordered points reverses their strict order. -/
private theorem point_lt {first second : Fraction.Rational} (ordered : first < second) :
    point second < point first := Fraction.Order.Arithmetic.sub_lt_sub_left_direct ordered 1

/-- Reversing and reflecting a strictly sorted cut list preserves strict sorting. -/
theorem cuts_sorted : ∀ cuts : List Fraction.Rational, cuts.Pairwise (· < ·) →
    (cuts.reverse.map point).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | head :: tail, sorted => by
      rw [Reverse.reverse_cons, Map.map_append]
      change (tail.reverse.map point ++ [point head]).Pairwise (· < ·)
      apply Pairwise.pairwise_append (cuts_sorted tail (List.pairwise_cons.mp sorted).2)
        (Pairwise.pairwise_singleton _ _)
      intro left leftMember right rightMember
      obtain ⟨original, originalMember, equal⟩ := Map.mem_map.mp leftMember
      have inTail := (Reverse.mem_reverse tail).mp originalMember
      have rightEq := Membership.mem_singleton.mp rightMember
      rw [← equal, rightEq]
      exact point_lt ((List.pairwise_cons.mp sorted).1 original inTail)

/-- Extending an interval chain adds its final endpoint as the final cut. -/
private theorem intervals_append (start middle finish : Fraction.Rational) : ∀ cuts,
    Interval.intervalsBetween start middle cuts ++ [⟨middle, finish⟩] =
      Interval.intervalsBetween start finish (cuts ++ [middle])
  | [] => rfl
  | cut :: remaining => by
      change ⟨start, cut⟩ :: (Interval.intervalsBetween cut middle remaining ++ [⟨middle, finish⟩]) =
        ⟨start, cut⟩ :: Interval.intervalsBetween cut finish (remaining ++ [middle])
      rw [intervals_append cut middle finish remaining]

/-- Reflecting a reversed exact chain gives the chain through the reversed reflected cuts. -/
private theorem intervals_reflect (start finish : Fraction.Rational) : ∀ cuts,
    (Interval.intervalsBetween start finish cuts).reverse.map interval =
      Interval.intervalsBetween (point finish) (point start) (cuts.reverse.map point)
  | [] => rfl
  | cut :: remaining => by
      rw [Interval.intervalsBetween, Reverse.reverse_cons, Map.map_append,
        intervals_reflect cut finish remaining, Reverse.reverse_cons, Map.map_append]
      change Interval.intervalsBetween (point finish) (point cut) (remaining.reverse.map point) ++
          [⟨point cut, point start⟩] =
        Interval.intervalsBetween (point finish) (point start) (remaining.reverse.map point ++ [point cut])
      exact intervals_append _ _ _ _

/-- Reflect a normalized partition, retaining every original cut and interval occurrence in reverse order. -/
@[expose] def partition (original : Normalized) : Normalized where
  cuts := original.cuts.reverse.map point
  sorted := cuts_sorted original.cuts original.sorted
  inside := by
    intro reflected member
    obtain ⟨originalCut, originalMember, equal⟩ := Map.mem_map.mp member
    have inOriginal := (Reverse.mem_reverse original.cuts).mp originalMember
    have inside := original.inside originalCut inOriginal
    rw [← equal]
    constructor
    · exact Fraction.Order.Arithmetic.sub_pos_direct inside.2
    · have bound := Fraction.Order.Arithmetic.sub_lt_sub_left_direct inside.1 1
      have identity : (1 : Fraction.Rational) - 0 = 1 := by ring1
      rw [identity] at bound
      exact bound
  intervals := original.intervals.reverse.map interval
  intervals_eq := by
    rw [original.intervals_eq, intervals_reflect]
    have pointOne : point 1 = 0 := by unfold point; ring1
    have pointZero : point 0 = 1 := by unfold point; ring1
    rw [pointOne, pointZero]

/-- The reflected partition reads back the original interval occurrences in reverse order. -/
theorem partition_intervals (original : Normalized) :
    (partition original).intervals = original.intervals.reverse.map interval := rfl

end Purelib.Integration.Partition.Unit.Reverse

end
