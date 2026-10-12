module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Fold
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.BinaryPrefix.Dyadic
public import Purelib.Data.List.BinaryPrefix.Frontier
import Purelib.Data.List.BinaryPrefix.Truncation
public import Purelib.Measure.BinaryPrefix.Averaging
import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Weighted.Operations

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.List.Event
public import Purelib.Measure.Content.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

open Purelib.Data.List

open Purelib.Algebra

open Purelib.Data.Rat

section
public section

/-!
# Symbolic dyadic weight of raw CCL prefixes

This is the fair-bit valuation on the raw binary address tree.  It is a
symbolic prefix weight, not geometric area and not the pushforward of
Lebesgue measure through the CCL decoder.  The distinction is explicit in the
API.
-/

namespace Purelib.Measure.BinaryPrefix

open Purelib.Data in
open Purelib.Data.Rat in
/-- Sum the dyadic prefix weights of the exact ordered frontier list.

Repeated words contribute repeatedly; no prefix-freeness or normalization assumption is imposed. -/
@[expose] def rawFrontierWeight (frontier : List CCLMeasureWord) :
  Fraction.Rational :=
  (frontier.map List.BinaryPrefix.rawPrefixWeight).sum

open Purelib in
open Purelib.Data in
/-- Retain a binary word as a weighted atom with its nonnegative dyadic prefix weight. -/
@[expose] def rawPrefixAtom (word : CCLMeasureWord) :
  Measure.Weighted CCLMeasureWord where
  item := word
  weight := List.BinaryPrefix.rawPrefixWeight word
  nonnegative := List.BinaryPrefix.rawPrefixWeight_nonneg word

section
open Purelib
open Purelib.Data
open Purelib.Measure
/-- Build finite content from the exact ordered frontier and its original dyadic prefix weights. -/
@[expose] def rawPrefixContent (frontier : List CCLMeasureWord) :
    Measure.Content CCLMeasureWord where
  atoms := frontier.map rawPrefixAtom

/-- The content's total is the sum of the original frontier's dyadic prefix weights. -/
theorem rawPrefixContent_total (frontier : List CCLMeasureWord) :
    (rawPrefixContent frontier).total = rawFrontierWeight frontier := by
  induction frontier with
  | nil => rfl
  | cons word remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, rawPrefixContent, Content.total,
        Measure.totalWeight, List.map_cons, rawPrefixAtom,
        rawFrontierWeight, List.sum_cons] at *
      rw [inductionHypothesis]

end

open Purelib.Data in
open Purelib.Measure in
/-- Every finite frontier has nonnegative total dyadic prefix weight. -/
theorem rawFrontierWeight_nonneg (frontier : List CCLMeasureWord)
  :
    0 ≤ rawFrontierWeight frontier := by
  induction frontier with
  | nil => exact le_rfl
  | cons word remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, rawFrontierWeight, List.map_cons, List.sum_cons] at *
      exact add_nonneg (List.BinaryPrefix.rawPrefixWeight_nonneg word) inductionHypothesis

open Purelib.Data in
/-- Replace the designated frontier word by its false and true extensions, retaining both surrounding lists. -/
@[expose] def splitRawFrontier (before after : List
  CCLMeasureWord) (word : CCLMeasureWord) : List CCLMeasureWord :=
  before ++ [word ++ [false], word ++ [true]] ++ after

open Purelib.Data
open Purelib.Measure
/-- Replacing one prefix by its two children preserves the exact frontier's total dyadic weight. -/
theorem splitRawFrontier_weight (before after : List
  CCLMeasureWord) (word : CCLMeasureWord) :
    rawFrontierWeight (splitRawFrontier before after word) =
      rawFrontierWeight (before ++ [word] ++ after) := by
  dsimp only [splitRawFrontier, rawFrontierWeight]
  simp only [-eq_self, -iff_self, Map.map_append, Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc,
    List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]; try rfl
  rw [List.BinaryPrefix.rawPrefixWeight_children_add]

/-- Replacing one prefix by its two children preserves the associated content's total mass. -/
theorem splitRawFrontier_content_total
    (before after : List CCLMeasureWord) (word : CCLMeasureWord) :
    (rawPrefixContent (splitRawFrontier before after word)).total =
      (rawPrefixContent (before ++ [word] ++ after)).total := by
  rw [rawPrefixContent_total, rawPrefixContent_total,
    splitRawFrontier_weight]
end Purelib.Measure.BinaryPrefix

end

section
public section

/-!
# Explicit finite-depth raw-prefix contents

For a supplied raw prefix and natural depth, `rawExtensions` generates the
complete displayed binary frontier below that prefix.  Its total dyadic
content is exactly the prefix weight, independently of the chosen finite
depth.  This is a finite conservation theorem, not a statement about an
infinite bit space.
-/

namespace Purelib.Measure.BinaryPrefix

open Purelib.Data in
open Purelib.Data.Rat in
/-- Every extension at the specified depth has the stem's prefix weight times one half raised to that depth. -/
theorem rawExtensions_member_weight (stem : CCLMeasureWord) (depth
  : Nat)
    (word : CCLMeasureWord) (member : word ∈ List.BinaryPrefix.rawExtensions stem depth) :
    List.BinaryPrefix.rawPrefixWeight word =
      List.BinaryPrefix.rawPrefixWeight stem * (1 / 2 : Fraction.Rational) ^ depth := by
  unfold List.BinaryPrefix.rawPrefixWeight
  rw [List.BinaryPrefix.rawExtensions_word_length stem depth word member, pow_add]

open Purelib.Data in
open Purelib.Measure in
/-- The complete fixed-depth extension frontier has total weight equal to the original stem weight. -/
theorem rawExtensions_weight (stem : CCLMeasureWord) : ∀ depth :
  Nat,
    rawFrontierWeight (List.BinaryPrefix.rawExtensions stem depth) = List.BinaryPrefix.rawPrefixWeight stem
  | 0 => by
      simp only [-eq_self, -iff_self, List.BinaryPrefix.rawExtensions, rawFrontierWeight, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]; try rfl
  | depth + 1 => by
      simp only [-eq_self, -iff_self, List.BinaryPrefix.rawExtensions, rawFrontierWeight, Map.map_append,
        Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc]; try rfl
      change rawFrontierWeight (List.BinaryPrefix.rawExtensions (stem ++ [false]) depth) +
          rawFrontierWeight (List.BinaryPrefix.rawExtensions (stem ++ [true]) depth) =
        List.BinaryPrefix.rawPrefixWeight stem
      rw [rawExtensions_weight (stem ++ [false]) depth,
        rawExtensions_weight (stem ++ [true]) depth,
        List.BinaryPrefix.rawPrefixWeight_children_add]

section
open Purelib
open Purelib.Data
section
open Purelib.Measure
/-- The two children's mass for a parent-pulled event equals the selected parent weight. -/
private theorem eventWeight_rawChildren_parent
    (word : CCLMeasureWord) (event : CCLMeasureWord → Bool) :
    Measure.eventWeight
        ((List.BinaryPrefix.rawChildren word).map rawPrefixAtom)
        (fun child => event (List.BinaryPrefix.rawParent child)) =
      match event word with
      | true => List.BinaryPrefix.rawPrefixWeight word
      | false => 0 := by
  cases selected : event word
  · simp only [-eq_self, -iff_self, List.BinaryPrefix.rawChildren, List.map_cons, List.map_nil,
      Measure.eventWeight, rawPrefixAtom,
      List.BinaryPrefix.rawParent_append_bit, selected, zero_add]; try rfl
  · simp only [-eq_self, -iff_self, List.BinaryPrefix.rawChildren, List.map_cons, List.map_nil,
      Measure.eventWeight, List.BinaryPrefix.rawParent_append_bit, selected,
      rawPrefixAtom, add_zero]; try rfl
    exact List.BinaryPrefix.rawPrefixWeight_children_add word

/-- Measuring a parent-pulled event on all frontier children recovers its original frontier mass. -/
private theorem eventWeight_rawChildFrontier_parent
    (event : CCLMeasureWord → Bool) : ∀ words : List CCLMeasureWord,
    Measure.eventWeight
        ((words.flatMap List.BinaryPrefix.rawChildren).map rawPrefixAtom)
        (fun child => event (List.BinaryPrefix.rawParent child)) =
      Measure.eventWeight (words.map rawPrefixAtom) event
  | [] => rfl
  | word :: remaining => by
      rw [Flatten.flatMap_cons, Map.map_append,
        Measure.eventWeight_append,
        eventWeight_rawChildren_parent word event,
        eventWeight_rawChildFrontier_parent event remaining]
      rfl

end

open Purelib.Data.Rat
open Purelib.Measure
/-- Selecting the true child and a parent-pulled event gives one half of the selected parent weight. -/
private theorem eventWeight_rawChildren_lastTrue_parent
    (word : CCLMeasureWord) (event : CCLMeasureWord → Bool) :
    Measure.eventWeight
        ((List.BinaryPrefix.rawChildren word).map rawPrefixAtom)
        (fun child => List.BinaryPrefix.rawLastBit child && event (List.BinaryPrefix.rawParent child)) =
      (1 / 2 : Fraction.Rational) *
        (match event word with
        | true => List.BinaryPrefix.rawPrefixWeight word
        | false => 0) := by
  cases selected : event word
  · simp only [-eq_self, -iff_self, List.BinaryPrefix.rawChildren, List.map_cons, List.map_nil,
      Measure.eventWeight, rawPrefixAtom,
      List.BinaryPrefix.rawLastBit_append_bit, List.BinaryPrefix.rawParent_append_bit, selected,
      Bool.and_false, zero_add, mul_zero]; try rfl
  · simp only [-eq_self, -iff_self, List.BinaryPrefix.rawChildren, List.map_cons, List.map_nil,
      Measure.eventWeight, rawPrefixAtom,
      List.BinaryPrefix.rawLastBit_append_bit, List.BinaryPrefix.rawParent_append_bit, selected,
      Bool.false_and, Bool.true_and, add_zero, List.BinaryPrefix.rawPrefixWeight_child]; try rfl
    ring1

/-- Selecting last-true children and a parent event gives one half of the original frontier event mass. -/
theorem eventWeight_rawChildFrontier_lastTrue_parent
    (event : CCLMeasureWord → Bool) : ∀ words : List CCLMeasureWord,
    Measure.eventWeight
        ((words.flatMap List.BinaryPrefix.rawChildren).map rawPrefixAtom)
        (fun child => List.BinaryPrefix.rawLastBit child && event (List.BinaryPrefix.rawParent child)) =
      (1 / 2 : Fraction.Rational) *
        Measure.eventWeight (words.map rawPrefixAtom) event
  | [] => by
      change (0 : Fraction.Rational) = (1 / 2 : Fraction.Rational) * 0
      exact (Fraction.Field.mul_zero_direct _).symm
  | word :: remaining => by
      rw [Flatten.flatMap_cons, Map.map_append,
        Measure.eventWeight_append,
        eventWeight_rawChildren_lastTrue_parent word event,
        eventWeight_rawChildFrontier_lastTrue_parent event remaining]
      simp only [-eq_self, -iff_self, List.map_cons, Measure.eventWeight,
        rawPrefixAtom]; try rfl
      cases event word <;> simp only [-eq_self, -iff_self, zero_add] <;> ring1

/-- Integrating a parent-pulled observable over two children gives its original value times parent weight. -/
private theorem expectationWeight_rawChildren_parent
    (word : CCLMeasureWord) (value : CCLMeasureWord → Fraction.Rational) :
    Distribution.expectationWeight
        ((List.BinaryPrefix.rawChildren word).map rawPrefixAtom)
        (fun child => value (List.BinaryPrefix.rawParent child)) =
      List.BinaryPrefix.rawPrefixWeight word * value word := by
  simp only [-eq_self, -iff_self, List.BinaryPrefix.rawChildren, List.map_cons, List.map_nil,
    Distribution.expectationWeight,
    List.BinaryPrefix.rawParent_append_bit, rawPrefixAtom, add_zero]; try rfl
  rw [← add_mul, List.BinaryPrefix.rawPrefixWeight_children_add]

/-- Integrating a parent-pulled observable over the child frontier preserves the original weighted integral. -/
private theorem expectationWeight_rawChildFrontier_parent
    (value : CCLMeasureWord → Fraction.Rational) : ∀ words : List CCLMeasureWord,
    Distribution.expectationWeight
        ((words.flatMap List.BinaryPrefix.rawChildren).map rawPrefixAtom)
        (fun child => value (List.BinaryPrefix.rawParent child)) =
      Distribution.expectationWeight
        (words.map rawPrefixAtom) value
  | [] => rfl
  | word :: remaining => by
      rw [Flatten.flatMap_cons, Map.map_append,
        Measure.expectationWeight_append,
        expectationWeight_rawChildren_parent word value,
        expectationWeight_rawChildFrontier_parent value remaining]
      rfl

end

open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The two children's weighted integral is the parent weight times the fair child mean. -/
private theorem expectationWeight_rawChildren_value
    (word : CCLMeasureWord) (value : CCLMeasureWord → Fraction.Rational) :
    Distribution.expectationWeight
        ((List.BinaryPrefix.rawChildren word).map rawPrefixAtom) value =
      List.BinaryPrefix.rawPrefixWeight word * BinaryPrefix.rawChildMean value word := by
  simp only [-eq_self, -iff_self, List.BinaryPrefix.rawChildren, List.map_cons, List.map_nil,
    Distribution.expectationWeight,
    rawPrefixAtom, add_zero]; try rfl
  rw [List.BinaryPrefix.rawPrefixWeight_child, List.BinaryPrefix.rawPrefixWeight_child]
  unfold BinaryPrefix.rawChildMean
  ring1

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The child frontier integral equals the original frontier integral of the fair child mean. -/
private theorem expectationWeight_rawChildFrontier_value
    (value : CCLMeasureWord → Fraction.Rational) : ∀ words : List CCLMeasureWord,
    Distribution.expectationWeight
        ((words.flatMap List.BinaryPrefix.rawChildren).map rawPrefixAtom) value =
      Distribution.expectationWeight
        (words.map rawPrefixAtom) (BinaryPrefix.rawChildMean value)
  | [] => rfl
  | word :: remaining => by
      rw [Flatten.flatMap_cons, Map.map_append,
        Measure.expectationWeight_append,
        expectationWeight_rawChildren_value word value,
        expectationWeight_rawChildFrontier_value value remaining]
      rfl

open Purelib in
open Purelib.Data in
open Purelib.Measure in
/-- Retain all fixed-depth extensions of the exact stem, weighted by their original dyadic prefix weights. -/
@[expose] def rawExtensionContent (stem : CCLMeasureWord) (depth :
  Nat) :
    Measure.Content CCLMeasureWord :=
  rawPrefixContent (List.BinaryPrefix.rawExtensions stem depth)

open Purelib.Data in
open Purelib.Measure in
/-- The complete extension content has total mass equal to the exact stem weight. -/
theorem rawExtensionContent_total (stem : CCLMeasureWord) (depth :
  Nat) :
    (rawExtensionContent stem depth).total = List.BinaryPrefix.rawPrefixWeight stem := by
    rw [rawExtensionContent, rawPrefixContent_total,
    rawExtensions_weight]

open Purelib in
open Purelib.Data in
open Purelib.Measure in
/-- Parent pullback preserves event measurements between consecutive extension depths. -/
theorem rawExtensionContent_measure_parent
    (stem : CCLMeasureWord) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (rawExtensionContent stem (depth + 1)).measure
        (fun word => event (List.BinaryPrefix.rawParent word)) =
      (rawExtensionContent stem depth).measure event := by
  unfold rawExtensionContent rawPrefixContent
  change Measure.eventWeight
      ((List.BinaryPrefix.rawExtensions stem (depth + 1)).map rawPrefixAtom)
        (fun word => event (List.BinaryPrefix.rawParent word)) =
    Measure.eventWeight
      ((List.BinaryPrefix.rawExtensions stem depth).map rawPrefixAtom) event
  rw [List.BinaryPrefix.rawExtensions_succ_children]
  exact eventWeight_rawChildFrontier_parent event (List.BinaryPrefix.rawExtensions stem depth)

section
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Measure
/-- Parent pullback preserves observable integrals between consecutive extension depths. -/
theorem rawExtensionContent_integral_parent
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (rawExtensionContent stem (depth + 1)).integral
        (fun word => value (List.BinaryPrefix.rawParent word)) =
      (rawExtensionContent stem depth).integral value := by
  unfold rawExtensionContent rawPrefixContent
  change Distribution.expectationWeight
      ((List.BinaryPrefix.rawExtensions stem (depth + 1)).map rawPrefixAtom)
        (fun word => value (List.BinaryPrefix.rawParent word)) =
    Distribution.expectationWeight
      ((List.BinaryPrefix.rawExtensions stem depth).map rawPrefixAtom) value
  rw [List.BinaryPrefix.rawExtensions_succ_children]
  exact expectationWeight_rawChildFrontier_parent value
    (List.BinaryPrefix.rawExtensions stem depth)

/-- The child-mean integral at one depth equals the observable integral at the next depth. -/
theorem rawExtensionContent_integral_childMean
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (rawExtensionContent stem depth).integral (BinaryPrefix.rawChildMean value) =
      (rawExtensionContent stem (depth + 1)).integral value := by
  unfold rawExtensionContent rawPrefixContent
  change Distribution.expectationWeight
      ((List.BinaryPrefix.rawExtensions stem depth).map rawPrefixAtom) (BinaryPrefix.rawChildMean value) =
    Distribution.expectationWeight
      ((List.BinaryPrefix.rawExtensions stem (depth + 1)).map rawPrefixAtom) value
  rw [List.BinaryPrefix.rawExtensions_succ_children]
  exact (expectationWeight_rawChildFrontier_value value
    (List.BinaryPrefix.rawExtensions stem depth)).symm

end

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- For an explicitly uniform-weight frontier, event mass equals selected occurrence count times that common weight. -/
theorem eventWeight_map_rawPrefixAtom_eq_count_mul
    (words : List CCLMeasureWord) (event : CCLMeasureWord → Bool) (unit :
      Fraction.Rational)
    (equalWeight : ∀ word, word ∈ words → List.BinaryPrefix.rawPrefixWeight word = unit) :
    Measure.eventWeight (words.map rawPrefixAtom) event =
      (Data.List.rawFrontierEventCount words event : Fraction.Rational) * unit := by
  induction words with
  | nil =>
      simp only [-eq_self, -iff_self, List.map_nil, Measure.eventWeight,
        Data.List.rawFrontierEventCount, Nat.cast_zero, zero_mul]; try rfl
  | cons word remaining inductionHypothesis =>
      have headWeight := equalWeight word List.mem_cons_self
      have tailWeight : ∀ candidate, candidate ∈ remaining →
          List.BinaryPrefix.rawPrefixWeight candidate = unit := by
        intro candidate member
        exact equalWeight candidate (List.mem_cons_of_mem word member)
      have tail := inductionHypothesis tailWeight
      clear equalWeight tailWeight
      cases selected : event word
      · simp only [-eq_self, -iff_self, List.map_cons, Measure.eventWeight,
          rawPrefixAtom, selected, Data.List.rawFrontierEventCount, if_neg (by decide : false ≠ true),
            zero_add]
        exact tail
      · simp only [-eq_self, -iff_self, List.map_cons, Measure.eventWeight,
          rawPrefixAtom, selected, Data.List.rawFrontierEventCount, if_pos (rfl : true = true),
          NatCast.add, Nat.cast_one]; try rfl
        rw [headWeight, tail]
        ring1

end Purelib.Measure.BinaryPrefix

end
