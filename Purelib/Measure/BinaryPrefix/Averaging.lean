module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

section
@[expose] public section

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
/-- Average the observable on the two one-bit extensions of the exact input word.

Each branch has rational weight one half; the original observable is evaluated separately on the false and true
extensions. -/
def rawChildMean (value : CCLMeasureWord → Fraction.Rational)
  (word : CCLMeasureWord) : Fraction.Rational :=
  (1 / 2 : Fraction.Rational) * value (word ++ [false]) +
    (1 / 2 : Fraction.Rational) * value (word ++ [true])

section
open Purelib
open Purelib.Data
section
open Purelib.Data.Rat
/-- The square of the two-child mean is bounded by the two-child mean of squares. -/
theorem rawChildMean_sq_le (value : CCLMeasureWord →
  Fraction.Rational) (word : CCLMeasureWord) :
    rawChildMean value word ^ 2 ≤
      rawChildMean (fun child => value child ^ 2) word := by
  let half : Fraction.Rational := 1 / 2
  let leftValue := value (word ++ [false])
  let rightValue := value (word ++ [true])
  change (half * leftValue + half * rightValue) ^ 2 ≤
    half * leftValue ^ 2 + half * rightValue ^ 2
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  have halfSubSquare : half - half ^ 2 = half ^ 2 := by
    decide
  have differenceIdentity :
      half * leftValue ^ 2 + half * rightValue ^ 2 -
          (half * leftValue + half * rightValue) ^ 2 =
        half ^ 2 * (leftValue - rightValue) ^ 2 := by
    calc
      half * leftValue ^ 2 + half * rightValue ^ 2 -
            (half * leftValue + half * rightValue) ^ 2 =
          (half - half ^ 2) * leftValue ^ 2 +
            (half - half ^ 2) * rightValue ^ 2 -
              2 * half ^ 2 * leftValue * rightValue := by ring1
      _ = half ^ 2 * leftValue ^ 2 + half ^ 2 * rightValue ^ 2 -
            2 * half ^ 2 * leftValue * rightValue := by
        rw [halfSubSquare]
      _ = half ^ 2 * (leftValue - rightValue) ^ 2 := by ring1
  rw [differenceIdentity]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct half)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Iterate fair two-child averaging for the supplied finite number of levels.

The successor step first averages each pair of children, then applies the retained number of remaining averaging steps.
-/
def rawBackwardMean : Nat → (CCLMeasureWord → Fraction.Rational) →
  CCLMeasureWord → Fraction.Rational
  | 0, value => value
  | extra + 1, value => rawBackwardMean extra (rawChildMean value)

/-- Subtract the squared child mean from the child mean of squares. -/
def rawChildVariance (value : CCLMeasureWord → Fraction.Rational)
  (word : CCLMeasureWord) : Fraction.Rational :=
  rawChildMean (fun child => value child ^ 2) word -
    rawChildMean value word ^ 2

/-- The fair two-child variance is nonnegative at every word. -/
theorem rawChildVariance_nonnegative
    (value : CCLMeasureWord → Fraction.Rational) (word : CCLMeasureWord) :
    0 ≤ rawChildVariance value word :=
  Fraction.Order.Arithmetic.sub_nonneg_direct (rawChildMean_sq_le value word)

/-- A pointwise nonnegative observable has nonnegative two-child mean. -/
theorem rawChildMean_nonnegative (value : CCLMeasureWord →
  Fraction.Rational)
    (nonnegative : ∀ word, 0 ≤ value word) (word : CCLMeasureWord) :
    0 ≤ rawChildMean value word := by
  unfold rawChildMean
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (nonnegative (word ++ [false])))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (nonnegative (word ++ [true])))

/-- Accumulate the conditional child variances through a finite binary refinement depth.

At a successor depth, add the backward mean of the child variance to the remaining backward variance of the child mean.
-/
def rawBackwardVariance : Nat → (CCLMeasureWord →
  Fraction.Rational) → CCLMeasureWord → Fraction.Rational
  | 0, _ => fun _ => 0
  | extra + 1, value => fun word =>
      rawBackwardMean extra (rawChildVariance value) word +
        rawBackwardVariance extra (rawChildMean value) word

/-- Pointwise equal observables have equal two-child means. -/
theorem rawChildMean_congr (left right : CCLMeasureWord →
  Fraction.Rational)
    (pointwise : ∀ word, left word = right word) (word : CCLMeasureWord) :
    rawChildMean left word = rawChildMean right word := by
  unfold rawChildMean
  rw [pointwise (word ++ [false]), pointwise (word ++ [true])]

/-- Pointwise equal observables have equal two-child variances. -/
theorem rawChildVariance_congr (left right : CCLMeasureWord →
  Fraction.Rational)
    (pointwise : ∀ word, left word = right word) (word : CCLMeasureWord) :
    rawChildVariance left word = rawChildVariance right word := by
  unfold rawChildVariance
  rw [rawChildMean_congr _ _
      (fun child => congrArg (fun value => value ^ 2) (pointwise child)) word,
    rawChildMean_congr left right pointwise word]

/-- Pointwise equal observables have equal backward means at every finite depth. -/
theorem rawBackwardMean_congr (left right : CCLMeasureWord →
  Fraction.Rational)
    (pointwise : ∀ word, left word = right word) :
    ∀ (extra : Nat) (word : CCLMeasureWord),
      rawBackwardMean extra left word = rawBackwardMean extra right word
  | 0, word => pointwise word
  | extra + 1, word =>
      rawBackwardMean_congr (rawChildMean left)
        (rawChildMean right)
        (rawChildMean_congr left right pointwise) extra word

/-- Pointwise equal observables have equal accumulated backward variances. -/
theorem rawBackwardVariance_congr (left right : CCLMeasureWord →
  Fraction.Rational)
    (pointwise : ∀ word, left word = right word) :
    ∀ (extra : Nat) (word : CCLMeasureWord),
      rawBackwardVariance extra left word =
        rawBackwardVariance extra right word
  | 0, word => rfl
  | extra + 1, word => by
      change
        rawBackwardMean extra (rawChildVariance left) word +
            rawBackwardVariance extra (rawChildMean left) word =
          rawBackwardMean extra (rawChildVariance right) word +
            rawBackwardVariance extra (rawChildMean right) word
      rw [rawBackwardMean_congr _ _
          (rawChildVariance_congr left right pointwise) extra word,
        rawBackwardVariance_congr (rawChildMean left)
          (rawChildMean right)
          (rawChildMean_congr left right pointwise) extra word]

/-- Finite backward averaging preserves pointwise nonnegativity. -/
theorem rawBackwardMean_nonnegative (value : CCLMeasureWord →
  Fraction.Rational)
    (nonnegative : ∀ word, 0 ≤ value word) :
    ∀ (extra : Nat) (word : CCLMeasureWord),
      0 ≤ rawBackwardMean extra value word
  | 0, word => nonnegative word
  | extra + 1, word =>
      rawBackwardMean_nonnegative (rawChildMean value)
        (rawChildMean_nonnegative value nonnegative) extra word

/-- Every finite accumulated backward variance is nonnegative. -/
theorem rawBackwardVariance_nonnegative (value : CCLMeasureWord →
  Fraction.Rational) :
    ∀ (extra : Nat) (word : CCLMeasureWord),
      0 ≤ rawBackwardVariance extra value word
  | 0, _ => le_rfl
  | extra + 1, word =>
      add_nonneg
        (rawBackwardMean_nonnegative (rawChildVariance value)
          (rawChildVariance_nonnegative value) extra word)
        (rawBackwardVariance_nonnegative (rawChildMean value) extra
          word)

/-- Averaging an observable pulled back along the parent map recovers its value on the original word. -/
theorem rawChildMean_parent (value : CCLMeasureWord →
  Fraction.Rational) (word : CCLMeasureWord) :
    rawChildMean (fun child => value (List.BinaryPrefix.rawParent child)) word = value word := by
  unfold rawChildMean
  change (1 / 2 : Fraction.Rational) * value (List.BinaryPrefix.rawParent (word ++ [false])) +
      (1 / 2 : Fraction.Rational) * value (List.BinaryPrefix.rawParent (word ++ [true])) = value word
  rw [List.BinaryPrefix.rawParent_append_bit, List.BinaryPrefix.rawParent_append_bit]
  have halves : (1 / 2 : Fraction.Rational) + 1 / 2 = 1 := by decide
  calc
    (1 / 2 : Fraction.Rational) * value word + 1 / 2 * value word =
        ((1 / 2 : Fraction.Rational) + 1 / 2) * value word := by ring1
    _ = 1 * value word := by rw [halves]
    _ = value word := by ring1

/-- An observable pulled back along the parent map has zero child variance. -/
theorem rawChildVariance_parent (value : CCLMeasureWord →
  Fraction.Rational) (word : CCLMeasureWord) :
    rawChildVariance (fun child => value (List.BinaryPrefix.rawParent child)) word = 0 := by
  unfold rawChildVariance
  rw [rawChildMean_parent (fun item => value item ^ 2),
    rawChildMean_parent value]
  ring1

end

/-- Every finite backward mean of the zero observable is zero. -/
theorem rawBackwardMean_zero : ∀ (extra : Nat) (word :
  CCLMeasureWord),
    rawBackwardMean extra (fun _ => 0) word = 0
  | 0, word => rfl
  | extra + 1, word => by
      change rawBackwardMean extra
          (rawChildMean (fun _ => 0)) word = 0
      calc
        rawBackwardMean extra (rawChildMean (fun _ => 0)) word =
            rawBackwardMean extra (fun _ => 0) word :=
          rawBackwardMean_congr _ _ (fun candidate => by
            unfold rawChildMean
            ring1) extra word
        _ = 0 := rawBackwardMean_zero extra word

open Purelib.Data.Rat
/-- Averaging an observable pulled back along the matching ancestor depth recovers its original value. -/
theorem rawBackwardMean_ancestor (value : CCLMeasureWord →
  Fraction.Rational) :
    ∀ (extra : Nat) (word : CCLMeasureWord),
      rawBackwardMean extra
          (fun descendant => value (List.BinaryPrefix.rawAncestor extra descendant)) word =
        value word
  | 0, word => rfl
  | extra + 1, word => by
      change rawBackwardMean extra
          (rawChildMean (fun descendant =>
            value (List.BinaryPrefix.rawAncestor extra (List.BinaryPrefix.rawParent descendant)))) word =
        value word
      calc
        rawBackwardMean extra
              (rawChildMean (fun descendant =>
                value (List.BinaryPrefix.rawAncestor extra (List.BinaryPrefix.rawParent descendant)))) word =
            rawBackwardMean extra
              (fun candidate => value (List.BinaryPrefix.rawAncestor extra candidate)) word :=
          rawBackwardMean_congr _ _ (fun candidate =>
            rawChildMean_parent
              (fun item => value (List.BinaryPrefix.rawAncestor extra item)) candidate) extra word
        _ = value word := rawBackwardMean_ancestor value extra word

/-- An observable pulled back along the matching ancestor depth has zero accumulated backward variance. -/
theorem rawBackwardVariance_ancestor (value : CCLMeasureWord →
  Fraction.Rational) :
    ∀ (extra : Nat) (word : CCLMeasureWord),
      rawBackwardVariance extra
          (fun descendant => value (List.BinaryPrefix.rawAncestor extra descendant)) word = 0
  | 0, word => rfl
  | extra + 1, word => by
      change
        rawBackwardMean extra
            (rawChildVariance (fun descendant =>
              value (List.BinaryPrefix.rawAncestor extra (List.BinaryPrefix.rawParent descendant)))) word +
          rawBackwardVariance extra
            (rawChildMean (fun descendant =>
              value (List.BinaryPrefix.rawAncestor extra (List.BinaryPrefix.rawParent descendant)))) word = 0
      rw [rawBackwardMean_congr _ _ (fun candidate =>
          rawChildVariance_parent
            (fun item => value (List.BinaryPrefix.rawAncestor extra item)) candidate) extra word,
        rawBackwardVariance_congr _ _ (fun candidate =>
          rawChildMean_parent
            (fun item => value (List.BinaryPrefix.rawAncestor extra item)) candidate) extra word,
        rawBackwardMean_zero,
        rawBackwardVariance_ancestor value extra word]
      ring1
end

end Purelib.Measure.BinaryPrefix

end
