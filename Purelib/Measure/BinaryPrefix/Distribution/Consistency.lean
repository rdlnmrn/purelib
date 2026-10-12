module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Measure.BinaryPrefix.Averaging
import Purelib.Measure.BinaryPrefix.Content
public import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.Content.Normalization.Basic
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation

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
open Purelib.Measure in
/-- Parent pullback preserves event probabilities between consecutive normalized extension depths. -/
theorem rawExtensionDistribution_probability_parent
    (stem : CCLMeasureWord) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability
        (fun word => event (List.BinaryPrefix.rawParent word)) =
      (BinaryPrefix.rawExtensionDistribution stem depth).probability event := by
  rw [BinaryPrefix.rawExtensionDistribution_probability,
    BinaryPrefix.rawExtensionDistribution_probability,
    BinaryPrefix.rawExtensionContent_measure_parent]

section
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Measure
/-- Parent pullback preserves expectations between consecutive normalized extension depths. -/
theorem rawExtensionDistribution_expectation_parent
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).expectation
        (fun word => value (List.BinaryPrefix.rawParent word)) =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation value := by
  unfold BinaryPrefix.rawExtensionDistribution
  rw [Content.normalize_expectation,
    Content.normalize_expectation,
    BinaryPrefix.rawExtensionContent_total, BinaryPrefix.rawExtensionContent_total,
    BinaryPrefix.rawExtensionContent_integral_parent]

/-- The child-mean expectation at one depth equals the observable expectation at the next depth. -/
theorem rawExtensionDistribution_expectation_childMean
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem depth).expectation (BinaryPrefix.rawChildMean value) =
      (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).expectation value := by
  unfold BinaryPrefix.rawExtensionDistribution
  rw [Content.normalize_expectation,
    Content.normalize_expectation,
    BinaryPrefix.rawExtensionContent_total, BinaryPrefix.rawExtensionContent_total,
    BinaryPrefix.rawExtensionContent_integral_childMean]

/-- Finite backward averaging transports an expectation from the deeper extension distribution to the retained earlier
depth. -/
theorem rawExtensionDistribution_expectation_backward
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) : ∀ extra : Nat,
    (BinaryPrefix.rawExtensionDistribution stem depth).expectation
        (BinaryPrefix.rawBackwardMean extra value) =
      (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).expectation value
  | 0 => rfl
  | extra + 1 => by
      change
        (BinaryPrefix.rawExtensionDistribution stem depth).expectation
            (BinaryPrefix.rawBackwardMean extra (BinaryPrefix.rawChildMean value)) =
          (BinaryPrefix.rawExtensionDistribution stem (depth + (extra + 1))).expectation
            value
      rw [rawExtensionDistribution_expectation_backward stem depth
        (BinaryPrefix.rawChildMean value) extra]
      simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
        rawExtensionDistribution_expectation_childMean
          stem (depth + extra) value

end

open Purelib.Data in
open Purelib.Measure in
/-- Pulling an event back along the specified ancestor depth preserves its earlier extension probability. -/
theorem rawExtensionDistribution_probability_ancestor
    (stem : CCLMeasureWord) (depth : Nat) (event : CCLMeasureWord → Bool) : ∀ extra
      : Nat,
    (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).probability
        (fun word => event (List.BinaryPrefix.rawAncestor extra word)) =
      (BinaryPrefix.rawExtensionDistribution stem depth).probability event
  | 0 => rfl
  | extra + 1 => by
      change
        (BinaryPrefix.rawExtensionDistribution stem ((depth + extra) + 1)).probability
            (fun word => event (List.BinaryPrefix.rawAncestor extra (List.BinaryPrefix.rawParent word))) =
          (BinaryPrefix.rawExtensionDistribution stem depth).probability event
      rw [rawExtensionDistribution_probability_parent stem (depth + extra)
        (fun word => event (List.BinaryPrefix.rawAncestor extra word))]
      exact rawExtensionDistribution_probability_ancestor stem depth event
        extra

open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Pulling an observable back along the specified ancestor depth preserves its earlier extension expectation. -/
theorem rawExtensionDistribution_expectation_ancestor
    (stem : CCLMeasureWord) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) : ∀ extra : Nat,
    (BinaryPrefix.rawExtensionDistribution stem (depth + extra)).expectation
        (fun word => value (List.BinaryPrefix.rawAncestor extra word)) =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation value
  | 0 => rfl
  | extra + 1 => by
      change
        (BinaryPrefix.rawExtensionDistribution stem ((depth + extra) + 1)).expectation
            (fun word => value (List.BinaryPrefix.rawAncestor extra (List.BinaryPrefix.rawParent word))) =
          (BinaryPrefix.rawExtensionDistribution stem depth).expectation value
      rw [rawExtensionDistribution_expectation_parent stem (depth + extra)
        (fun word => value (List.BinaryPrefix.rawAncestor extra word))]
      exact rawExtensionDistribution_expectation_ancestor stem depth value
        extra

open Purelib.Data in
open Purelib.Measure in
/-- Mapping deeper extensions to their retained ancestors preserves all event probabilities and expectations of the
earlier distribution. -/
theorem rawExtensionDistribution_mapAncestor_evaluationEquivalent
    (stem : CCLMeasureWord) (depth extra : Nat) :
    Distribution.EvaluationEquivalent
      ((BinaryPrefix.rawExtensionDistribution stem (depth + extra)).map
        (List.BinaryPrefix.rawAncestor extra))
      (BinaryPrefix.rawExtensionDistribution stem depth) where
  probability_eq event := by
    rw [Distribution.map_probability]
    exact rawExtensionDistribution_probability_ancestor
      stem depth event extra
  expectation_eq value := by
    rw [Distribution.map_expectation]
    exact rawExtensionDistribution_expectation_ancestor
      stem depth value extra
end Purelib.Measure.BinaryPrefix

end
