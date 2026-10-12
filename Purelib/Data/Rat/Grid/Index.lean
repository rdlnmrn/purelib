module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

/-!
# Successive rational grid indices

The original finite scan tests successive upper endpoints and retains the
first bounded index. Direct scalar certificates establish its containment.
-/

namespace Purelib.Data.Rat.Grid.Index

/-- Find a bounded grid-cell index by testing successive rational upper endpoints.

At each step, return the first cell when the value is at most its upper endpoint; otherwise advance the lower endpoint
by one side and recurse on the remaining count. The finite result retains the original index bound, with containment
requiring positive side length and the stated overall grid bounds. -/
@[expose] public def coordinateIndex (lower side value : Fraction.Rational) :
    (intervals : Nat) → Fin (intervals + 1)
  | 0 => 0
  | intervals + 1 =>
      if value ≤ lower + side then 0
      else (Purelib.Data.Rat.Grid.Index.coordinateIndex (lower + side) side value intervals).succ

/-- The selected positive-width grid cell contains the bounded rational value.

The lower endpoint and total grid cover bound the query value. The original
finite scan returns the first tested index, and successor cast identities
transport the same two endpoints through the remaining grid. -/
public theorem coordinateIndex_mem
    {lower side value : Fraction.Rational} (sidePositive : 0 < side) :
    ∀ (intervals : Nat), lower ≤ value →
      value ≤ lower + (intervals : Nat) * side →
      lower + ((Grid.Index.coordinateIndex lower side value intervals).val : Nat) * side ≤
          value ∧
        value ≤ lower +
          (((Grid.Index.coordinateIndex lower side value intervals).val : Nat) + 1) *
            side
  | 0, lowerBound, upperBound => by
      have valueEq : value = lower := by
        apply le_antisymm
        · simpa only [Nat.cast_zero, zero_mul, add_zero] using upperBound
        · exact lowerBound
      subst value
      constructor
      · change lower + (0 : Fraction.Rational) * side ≤ lower
        rewrite [MulZeroClass.zero_mul, add_zero]
        exact Fraction.Order.Basic.le_refl lower
      · simp only [Grid.Index.coordinateIndex, Fin.val_zero, Nat.cast_zero, zero_add,
          one_mul]
        exact le_add_of_nonneg_right sidePositive.le
  | intervals + 1, lowerBound, upperBound => by
      by_cases first : value ≤ lower + side
      · constructor
        · simpa only [Grid.Index.coordinateIndex, if_pos first, Fin.val_zero,
            Nat.cast_zero, zero_mul, add_zero] using lowerBound
        · simpa only [Grid.Index.coordinateIndex, if_pos first, Fin.val_zero,
            Nat.cast_zero, zero_add, Nat.cast_one, one_mul] using first
      · have nextLower : lower + side ≤ value := (lt_of_not_ge first).le
        have nextUpper : value ≤
            (lower + side) + (intervals : Nat) * side := by
          calc
            value ≤ lower + ((intervals + 1 : Nat) : Fraction.Rational) * side :=
              upperBound
            _ = (lower + side) + (intervals : Nat) * side := by
              rewrite [Nat.cast_succ]
              ring1
        have next := Purelib.Data.Rat.Grid.Index.coordinateIndex_mem sidePositive intervals nextLower
          nextUpper
        constructor
        · calc
            lower +
                ((Grid.Index.coordinateIndex lower side value (intervals + 1)).val : Nat) *
                  side =
              (lower + side) +
                ((Grid.Index.coordinateIndex (lower + side) side value intervals).val :
                  Nat) * side := by
                rw [Grid.Index.coordinateIndex, if_neg first]
                simp only [Fin.val_succ]
                rewrite [Nat.cast_succ]
                ring1
            _ ≤ value := next.1
        · calc
            value ≤ (lower + side) +
                (((Grid.Index.coordinateIndex (lower + side) side value intervals).val :
                  Nat) + 1) * side := next.2
            _ = lower +
                (((Grid.Index.coordinateIndex lower side value (intervals + 1)).val :
                  Nat) + 1) * side := by
                rw [Grid.Index.coordinateIndex, if_neg first]
                simp only [Fin.val_succ]
                rewrite [Nat.cast_succ]
                ring1

end Purelib.Data.Rat.Grid.Index
