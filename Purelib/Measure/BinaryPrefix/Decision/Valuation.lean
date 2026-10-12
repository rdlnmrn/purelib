module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.BinaryPrefix.Decision.Basic
public import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
public section

/-!
# A finite Boolean algebra of raw-prefix decisions

`RawEvent` is a finite binary decision tree.  Its valuation is computed by
finite recursion, assigning half of the current symbolic weight to each raw
bit branch.  It is deliberately not a set of completed bit streams and does
not assert that the CCL decoder preserves this symbolic valuation.
-/

namespace Purelib.Data.List.BinaryPrefix
namespace RawEvent

section
open Purelib.Data
open Purelib.Data.Rat
/-- Compute the rational weight of a finite Boolean decision tree by averaging its two branch weights.

Empty and full leaves contribute zero and one, respectively; each branch retains both exact child contributions with
factor one half. -/
@[expose] def weight : List.BinaryPrefix.RawEvent → Fraction.Rational
  | .empty => 0
  | .full => 1
  | .branch falseChild trueChild =>
      (weight falseChild + weight
        trueChild) * (1 / 2)

/-- Every finite raw decision event has nonnegative computed weight. -/
theorem weight_nonneg : ∀ event : List.BinaryPrefix.RawEvent, 0 ≤
  event.weight
  | .empty => le_rfl
  | .full => by decide
  | .branch falseChild trueChild =>
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (add_nonneg (weight_nonneg falseChild)
          (weight_nonneg trueChild))
        (by decide)

/-- Every finite raw decision event has computed weight at most one. -/
theorem weight_le_one : ∀ event : List.BinaryPrefix.RawEvent,
  event.weight ≤ 1
  | .empty => by decide
  | .full => le_rfl
  | .branch falseChild trueChild => by
      have sumLe : falseChild.weight + trueChild.weight ≤
          (1 : Fraction.Rational) + 1 :=
        Fraction.Order.Arithmetic.add_le_add_direct
          (weight_le_one falseChild)
            (weight_le_one trueChild)
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          sumLe (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
      calc
        (List.BinaryPrefix.RawEvent.branch falseChild trueChild).weight =
            (falseChild.weight + trueChild.weight) * (1 / 2) := rfl
        _ ≤ ((1 : Fraction.Rational) + 1) * (1 / 2) := scaled
        _ = 1 := by decide

/-- Complementing a raw decision event replaces its weight by one minus its original weight. -/
theorem weight_complement : ∀ event : List.BinaryPrefix.RawEvent,
    event.complement.weight = 1 - event.weight
  | .empty => by decide
  | .full => by decide
  | .branch falseChild trueChild => by
      rw [List.BinaryPrefix.RawEvent.complement, weight,
        weight_complement falseChild,
        weight_complement trueChild, weight]
      let half : Fraction.Rational := 1 / 2
      have halves : half + half = 1 := by decide
      change ((1 - falseChild.weight) + (1 - trueChild.weight)) * half =
        1 - (falseChild.weight + trueChild.weight) * half
      calc
        ((1 - falseChild.weight) + (1 - trueChild.weight)) * half =
            (half + half) -
              (falseChild.weight + trueChild.weight) * half := by ring1
        _ = 1 - (falseChild.weight + trueChild.weight) * half := by
          rw [halves]

/-- Union weight plus intersection weight equals the sum of the two original raw-event weights. -/
theorem weight_union_add_inter : ∀ left right :
  List.BinaryPrefix.RawEvent,
    (left.union right).weight + (left.inter right).weight =
      left.weight + right.weight
  | .empty, right => by
      simp only [-eq_self, -iff_self, List.BinaryPrefix.RawEvent.union, List.BinaryPrefix.RawEvent.inter,
        weight, zero_add, add_zero]; try rfl
  | .full, right => by
      simp only [-eq_self, -iff_self, List.BinaryPrefix.RawEvent.union, List.BinaryPrefix.RawEvent.inter,
        weight]; try rfl
  | .branch falseChild trueChild, .empty => by
      simp only [-eq_self, -iff_self, List.BinaryPrefix.RawEvent.union, List.BinaryPrefix.RawEvent.inter,
        weight, add_zero]; try rfl
  | .branch falseChild trueChild, .full => by
      simp only [-eq_self, -iff_self, List.BinaryPrefix.RawEvent.union, List.BinaryPrefix.RawEvent.inter,
        weight]; try rfl
      exact add_comm 1
        ((falseChild.weight + trueChild.weight) * (1 / 2))
  | .branch falseChild trueChild, .branch falseRight trueRight => by
      rw [List.BinaryPrefix.RawEvent.union, List.BinaryPrefix.RawEvent.inter, weight,
        weight, weight, weight]
      have falseIdentity := weight_union_add_inter falseChild falseRight
      have trueIdentity := weight_union_add_inter trueChild trueRight
      let half : Fraction.Rational := 1 / 2
      change
        ((falseChild.union falseRight).weight +
            (trueChild.union trueRight).weight) * half +
          ((falseChild.inter falseRight).weight +
            (trueChild.inter trueRight).weight) * half =
        (falseChild.weight + trueChild.weight) * half +
          (falseRight.weight + trueRight.weight) * half
      calc
        ((falseChild.union falseRight).weight +
              (trueChild.union trueRight).weight) * half +
            ((falseChild.inter falseRight).weight +
              (trueChild.inter trueRight).weight) * half =
            (((falseChild.union falseRight).weight +
                (falseChild.inter falseRight).weight) +
              ((trueChild.union trueRight).weight +
                (trueChild.inter trueRight).weight)) * half := by ring1
        _ = ((falseChild.weight + falseRight.weight) +
              (trueChild.weight + trueRight.weight)) * half := by
          rw [falseIdentity, trueIdentity]
        _ = (falseChild.weight + trueChild.weight) * half +
              (falseRight.weight + trueRight.weight) * half := by ring1

end

open Purelib.Data
/-- Raw-event union weight is additive when their exact intersection has zero weight. -/
theorem weight_union_of_inter_weight_zero {left right :
  List.BinaryPrefix.RawEvent}
    (disjoint : (left.inter right).weight = 0) :
    (left.union right).weight = left.weight + right.weight := by
  have valuation := weight_union_add_inter left right
  rw [disjoint, add_zero] at valuation
  exact valuation

/-- A decision event for one prefix has exactly that prefix's dyadic weight. -/
theorem ofPrefix_weight : ∀ word : List.BinaryPrefix.CCLMeasureWord,
    (List.BinaryPrefix.RawEvent.ofPrefix word).weight = List.BinaryPrefix.rawPrefixWeight word
  | [] => rfl
  | false :: remaining => by
      rw [List.BinaryPrefix.RawEvent.ofPrefix, weight,
        ofPrefix_weight remaining, weight]
      simp only [-eq_self, -iff_self, List.BinaryPrefix.rawPrefixWeight, List.length_cons, pow_succ, add_zero]; try rfl
  | true :: remaining => by
      rw [List.BinaryPrefix.RawEvent.ofPrefix, weight,
        ofPrefix_weight remaining, weight]
      simp only [-eq_self, -iff_self, List.BinaryPrefix.rawPrefixWeight, List.length_cons, pow_succ, zero_add]; try rfl

/-- The two immediate prefix-child decision events have weights summing to the original prefix-event weight. -/
theorem ofPrefix_children_weight (stem :
  List.BinaryPrefix.CCLMeasureWord) :
    (List.BinaryPrefix.RawEvent.ofPrefix (stem ++ [false])).weight +
      (List.BinaryPrefix.RawEvent.ofPrefix (stem ++ [true])).weight = (List.BinaryPrefix.RawEvent.ofPrefix stem).weight
        := by
  rw [ofPrefix_weight, ofPrefix_weight,
    ofPrefix_weight]
  exact List.BinaryPrefix.rawPrefixWeight_children_add stem
end RawEvent

end Purelib.Data.List.BinaryPrefix

end
