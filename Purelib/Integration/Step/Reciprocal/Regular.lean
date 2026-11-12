module
public import Purelib.Integration.Step.Reciprocal
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Map
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Regular pieces of the rational reciprocal step

Above a positive reciprocal tail only a finite prefix of the original cuts
can separate two rational queries. Avoiding those retained cuts forces their
exact reciprocal floors, and hence their original step readings, to agree.
-/

public section

namespace Purelib.Integration.Step.Reciprocal

open Purelib.Data.Rat

/-- A nonnegative integer is recovered from its natural readback. -/
private theorem integer_of_toNat (integer : Int) (nonnegative : 0 ≤ integer) :
    (integer.toNat : Int) = integer := by
  cases integer with
  | ofNat _ => rfl
  | negSucc _ => cases nonnegative

/-- Rational floors preserve the original weak order. -/
private theorem floor_mono {first second : Fraction.Rational} (ordered : first ≤ second) :
    Rounding.Floor.floor first ≤ Rounding.Floor.floor second := by
  apply (Rounding.Floor.intCast_le_iff_floor (Rounding.Floor.floor first) second).mp
  exact ((Rounding.Floor.intCast_le_iff_floor (Rounding.Floor.floor first) first).mpr
    (Int.le_refl _)).trans ordered

/-- A positive unit-interval point has reciprocal floor at least one. -/
private theorem floor_reciprocal_ge_one (point : Fraction.Rational) (positive : 0 < point) (upper : point ≤ 1) :
    1 ≤ Rounding.Floor.floor (1 / point) := by
  apply (Rounding.Floor.intCast_le_iff_floor 1 (1 / point)).mp
  rw [show ((1 : Int) : Fraction.Rational) = 1 by decide]
  apply (Fraction.Order.Field.le_div_iff_pos positive).mpr
  rw [Fraction.Field.one_mul]
  exact upper

/-- A natural integer strictly above an integer at least one is at least two. -/
private theorem index_ge_two (index : Nat) (previous : Int) (previousBound : 1 ≤ previous)
    (strict : previous < (index : Int)) : 2 ≤ index := by
  omega0

/-- A reciprocal tail and finitely many cuts determine each regular piece's exact floor.

Both endpoints are rational points above the original tail and in the unit
interval. If their closed interval contains none of the finite cuts from
`1/2` through `1/(count-1)`, the two reciprocal floors agree. -/
theorem floor_eq_of_no_cuts (count : Nat) (countBound : 2 ≤ count)
    (first second : Fraction.Rational)
    (aboveTail : 1 / (count : Fraction.Rational) < first)
    (ordered : first ≤ second) (upper : second ≤ 1)
    (noCuts : ∀ point ∈ cuts (count - 2), ¬ (first ≤ point ∧ point ≤ second)) :
    Rounding.Floor.floor (1 / first) = Rounding.Floor.floor (1 / second) := by
  have countPositive : 0 < (count : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.lt_of_lt_of_le (by decide : 0 < 2) countBound)
  have firstPositive : 0 < first :=
    (Fraction.Order.Field.div_pos_direct (by decide) countPositive).trans aboveTail
  have secondPositive : 0 < second := firstPositive.trans_le ordered
  have reciprocalOrdered : 1 / second ≤ 1 / first :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct (by decide) firstPositive ordered
  have floorOrdered := floor_mono reciprocalOrdered
  by_cases equal : Rounding.Floor.floor (1 / first) = Rounding.Floor.floor (1 / second)
  · exact equal
  · have strict : Rounding.Floor.floor (1 / second) < Rounding.Floor.floor (1 / first) := by
      omega0
    let index := (Rounding.Floor.floor (1 / first)).toNat
    have indexEq : (index : Int) = Rounding.Floor.floor (1 / first) :=
      integer_of_toNat _ (floor_nonnegative first firstPositive)
    have floorSecondBound := floor_reciprocal_ge_one second secondPositive upper
    have indexBound : 2 ≤ index := index_ge_two index _ floorSecondBound (by rw [indexEq]; exact strict)
    have indexPositive : 0 < (index : Fraction.Rational) :=
      Fraction.Cast.Order.natCast_pos_direct (Nat.lt_of_lt_of_le (by decide : 0 < 2) indexBound)
    have floorLower : (index : Fraction.Rational) ≤ 1 / first := by
      have bound := Rounding.Floor.intCast_floor_le (1 / first)
      rw [← indexEq, Fraction.Cast.intCast_eq_fromInt, ← Fraction.Cast.natCast_eq_fromInt index] at bound
      exact bound
    have belowCount : 1 / first < (count : Fraction.Rational) := by
      apply (Fraction.Order.Field.div_lt_iff_pos firstPositive).mpr
      have paid := (Fraction.Order.Field.div_lt_iff_pos countPositive).mp aboveTail
      have identity : first * (count : Fraction.Rational) = (count : Fraction.Rational) * first := by ring1
      rw [identity] at paid
      exact paid
    have indexBelowCount : index < count :=
      Fraction.Cast.Order.natCast_lt_iff_direct.mp (floorLower.trans_lt belowCount)
    have successorBound : Rounding.Floor.floor (1 / second) + 1 ≤ (index : Int) := by
      rw [indexEq]
      exact Int.add_one_le_of_lt strict
    have castBound : ((Rounding.Floor.floor (1 / second) + 1 : Int) : Fraction.Rational) ≤
        (index : Fraction.Rational) := by
      have bound := (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).mpr successorBound
      rw [Fraction.Cast.intCast_eq_fromInt (index : Int), ← Fraction.Cast.natCast_eq_fromInt index] at bound
      exact bound
    have floorUpper := Rounding.Floor.lt_intCast_floor_add_one (1 / second)
    have secondReciprocalBound : 1 / second < (index : Fraction.Rational) := floorUpper.trans_le castBound
    have firstBeforeCut : first ≤ 1 / (index : Fraction.Rational) := by
      apply (Fraction.Order.Field.le_div_iff_pos indexPositive).mpr
      have paid := (Fraction.Order.Field.le_div_iff_pos firstPositive).mp floorLower
      have identity : (index : Fraction.Rational) * first = first * (index : Fraction.Rational) := by ring1
      rw [identity] at paid
      exact paid
    have cutBeforeSecond : 1 / (index : Fraction.Rational) ≤ second := by
      apply ((Fraction.Order.Field.div_lt_iff_pos indexPositive).mpr ?_).le
      have paid := (Fraction.Order.Field.div_lt_iff_pos secondPositive).mp secondReciprocalBound
      have identity : (index : Fraction.Rational) * second = second * (index : Fraction.Rational) := by ring1
      rw [identity] at paid
      exact paid
    have cutMember : 1 / (index : Fraction.Rational) ∈ cuts (count - 2) := by
      apply Purelib.Data.List.Map.mem_map.mpr
      refine ⟨index - 2, (Purelib.Data.List.Range.Basic.mem_range).mpr
        (Nat.sub_lt_sub_right indexBound indexBelowCount), ?_⟩
      change 1 / (((index - 2 + 2 : Nat) : Fraction.Rational)) = 1 / (index : Fraction.Rational)
      have identity : index - 2 + 2 = index := Nat.sub_add_cancel indexBound
      rw [identity]
    exact (noCuts _ cutMember ⟨firstBeforeCut, cutBeforeSecond⟩).elim

/-- Rational step readings agree on each cut-free regular piece above the reciprocal tail. -/
theorem value_eq_of_no_cuts (count : Nat) (countBound : 2 ≤ count)
    (first second : Fraction.Rational)
    (aboveTail : 1 / (count : Fraction.Rational) < first)
    (ordered : first ≤ second) (upper : second ≤ 1)
    (noCuts : ∀ point ∈ cuts (count - 2), ¬ (first ≤ point ∧ point ≤ second)) :
    value first = value second := by
  have countPositive : 0 < (count : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.lt_of_lt_of_le (by decide : 0 < 2) countBound)
  have firstPositive : 0 < first :=
    (Fraction.Order.Field.div_pos_direct (by decide) countPositive).trans aboveTail
  have secondPositive : 0 < second := firstPositive.trans_le ordered
  unfold value
  rw [if_pos firstPositive, if_pos secondPositive,
    floor_eq_of_no_cuts count countBound first second aboveTail ordered upper noCuts]

end Purelib.Integration.Step.Reciprocal

end
