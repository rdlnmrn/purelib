module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.BinaryPrefix.Averaging
public import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.BinaryPrefix.Distribution.Consistency

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Expectation
import Mathlib.Order.Basic
import Purelib.Measure.Distribution.Stability
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

section
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Measure
/-- Variance of the exact child average under the parent law is at most variance under the next-depth law. -/
theorem rawExtensionDistribution_variance_childMean
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem depth).variance (BinaryPrefix.rawChildMean value) ≤
      (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).variance value := by
  rw [(BinaryPrefix.rawExtensionDistribution stem depth).variance_eq_secondMoment_sub_sq,
    (BinaryPrefix.rawExtensionDistribution stem
      (depth + 1)).variance_eq_secondMoment_sub_sq]
  have secondMomentBound :
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
          (fun word => BinaryPrefix.rawChildMean value word ^ 2) ≤
        (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).expectation
          (fun word => value word ^ 2) := by
    calc
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
            (fun word => BinaryPrefix.rawChildMean value word ^ 2) ≤
          (BinaryPrefix.rawExtensionDistribution stem depth).expectation
            (BinaryPrefix.rawChildMean fun word => value word ^ 2) := by
        apply (BinaryPrefix.rawExtensionDistribution stem depth).expectation_mono
        intro atom member
        exact BinaryPrefix.rawChildMean_sq_le value atom.item
      _ = (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).expectation
            (fun word => value word ^ 2) :=
        BinaryPrefix.rawExtensionDistribution_expectation_childMean stem depth _
  have meanEqual :=
    BinaryPrefix.rawExtensionDistribution_expectation_childMean stem depth value
  rw [meanEqual]
  exact Fraction.Order.Arithmetic.sub_le_sub_right_direct secondMomentBound _

/-- Next-depth variance splits into expected child variance plus variance of the exact child average. -/
theorem rawExtensionDistribution_totalVariance_child
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).variance value =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
          (BinaryPrefix.rawChildVariance value) +
        (BinaryPrefix.rawExtensionDistribution stem depth).variance
          (BinaryPrefix.rawChildMean value) := by
  rw [(BinaryPrefix.rawExtensionDistribution stem
      (depth + 1)).variance_eq_secondMoment_sub_sq,
    (BinaryPrefix.rawExtensionDistribution stem depth).variance_eq_secondMoment_sub_sq]
  unfold BinaryPrefix.rawChildVariance
  rw [(BinaryPrefix.rawExtensionDistribution stem depth).expectation_sub,
    BinaryPrefix.rawExtensionDistribution_expectation_childMean stem depth
      (fun word => value word ^ 2),
    BinaryPrefix.rawExtensionDistribution_expectation_childMean stem depth value]
  ring1

/-- Variance of an iterated backward average is at most the original observable's variance at the corresponding deeper
law. -/
theorem rawExtensionDistribution_variance_backward
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) : ∀ extra : Nat,
    (BinaryPrefix.rawExtensionDistribution stem depth).variance
        (BinaryPrefix.rawBackwardMean extra value) ≤
      (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).variance value
  | 0 => le_rfl
  | extra + 1 => by
      change
        (BinaryPrefix.rawExtensionDistribution stem depth).variance
            (BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildMean value)) ≤
          (BinaryPrefix.rawExtensionDistribution stem (depth + (extra + 1))).variance
            value
      exact
        (rawExtensionDistribution_variance_backward stem depth
          (BinaryPrefix.rawChildMean value) extra).trans (by
            simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
              rawExtensionDistribution_variance_childMean
                stem (depth + extra) value)

/-- Deeper variance splits into expected retained backward variance plus variance of the exact backward average.

Both terms use the same original stem, starting depth and number of backward steps. -/
theorem rawExtensionDistribution_totalVariance_backward
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) : ∀ extra : Nat,
    (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).variance value =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
          (BinaryPrefix.rawBackwardVariance extra value) +
        (BinaryPrefix.rawExtensionDistribution stem depth).variance
          (BinaryPrefix.rawBackwardMean extra value)
  | 0 => by
      change (BinaryPrefix.rawExtensionDistribution stem depth).variance value =
        (BinaryPrefix.rawExtensionDistribution stem depth).expectation (fun _ => 0) +
          (BinaryPrefix.rawExtensionDistribution stem depth).variance value
      rw [(BinaryPrefix.rawExtensionDistribution stem depth).expectation_constant]
      ring1
  | extra + 1 => by
      change
        (BinaryPrefix.rawExtensionDistribution stem (depth + (extra + 1))).variance value =
          (BinaryPrefix.rawExtensionDistribution stem depth).expectation
              (fun word =>
                BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildVariance value) word +
                  BinaryPrefix.rawBackwardVariance extra (BinaryPrefix.rawChildMean value) word) +
            (BinaryPrefix.rawExtensionDistribution stem depth).variance
              (BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildMean value))
      calc
        (BinaryPrefix.rawExtensionDistribution stem
              (depth + (extra + 1))).variance value =
            (BinaryPrefix.rawExtensionDistribution stem (depth + extra + 1)).variance
              value := by
          congr 2
        _ = (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).expectation
              (BinaryPrefix.rawChildVariance value) +
            (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).variance
              (BinaryPrefix.rawChildMean value) :=
          rawExtensionDistribution_totalVariance_child
            stem (depth + extra) value
        _ = (BinaryPrefix.rawExtensionDistribution stem depth).expectation
              (BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildVariance value)) +
            ((BinaryPrefix.rawExtensionDistribution stem depth).expectation
                (BinaryPrefix.rawBackwardVariance extra (BinaryPrefix.rawChildMean value)) +
              (BinaryPrefix.rawExtensionDistribution stem depth).variance
                (BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildMean value))) := by
          rw [← BinaryPrefix.rawExtensionDistribution_expectation_backward stem depth
              (BinaryPrefix.rawChildVariance value) extra,
            rawExtensionDistribution_totalVariance_backward stem depth
              (BinaryPrefix.rawChildMean value) extra]
        _ = (BinaryPrefix.rawExtensionDistribution stem depth).expectation
              (fun word =>
                BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildVariance value) word +
                  BinaryPrefix.rawBackwardVariance extra (BinaryPrefix.rawChildMean value) word) +
            (BinaryPrefix.rawExtensionDistribution stem depth).variance
              (BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildMean value)) := by
          rw [(BinaryPrefix.rawExtensionDistribution stem depth).expectation_add]
          ring1
end

end Purelib.Measure.BinaryPrefix

end
