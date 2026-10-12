module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.List.BinaryPrefix.Frontier
import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.BinaryPrefix.Content
public import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.Weighted.Event

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

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

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- A true final bit and any parent event have joint probability one half times the original parent-event probability.

The laws retain the same original stem and successive extension depths, and the parent event is read from the exact
truncated word. -/
theorem rawExtensionDistribution_probability_lastTrue_and_parent
    (stem : CCLMeasureWord) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability
        (fun word => List.BinaryPrefix.rawLastBit word && event (List.BinaryPrefix.rawParent word)) =
      (1 / 2 : Fraction.Rational) *
        (BinaryPrefix.rawExtensionDistribution stem depth).probability event := by
  rw [BinaryPrefix.rawExtensionDistribution_probability,
    BinaryPrefix.rawExtensionDistribution_probability]
  change (Measure.eventWeight
      ((List.BinaryPrefix.rawExtensions stem (depth + 1)).map BinaryPrefix.rawPrefixAtom)
        (fun word => List.BinaryPrefix.rawLastBit word && event (List.BinaryPrefix.rawParent word))) /
      List.BinaryPrefix.rawPrefixWeight stem =
    (1 / 2 : Fraction.Rational) *
      (Measure.eventWeight
        ((List.BinaryPrefix.rawExtensions stem depth).map BinaryPrefix.rawPrefixAtom) event /
          List.BinaryPrefix.rawPrefixWeight stem)
  rw [List.BinaryPrefix.rawExtensions_succ_children,
    BinaryPrefix.eventWeight_rawChildFrontier_lastTrue_parent]
  change ((1 / 2 : Fraction.Rational) *
      Measure.eventWeight
        ((List.BinaryPrefix.rawExtensions stem depth).map BinaryPrefix.rawPrefixAtom) event) *
      (List.BinaryPrefix.rawPrefixWeight stem)⁻¹ =
    (1 / 2 : Fraction.Rational) *
      (Measure.eventWeight
        ((List.BinaryPrefix.rawExtensions stem depth).map BinaryPrefix.rawPrefixAtom) event *
          (List.BinaryPrefix.rawPrefixWeight stem)⁻¹)
  exact Fraction.Field.mul_assoc _ _ _

open Purelib.Data in
open Purelib.Measure in
/-- The last bit is true with probability one half under every positive-depth extension distribution. -/
theorem rawExtensionDistribution_probability_lastBit_true
    (stem : CCLMeasureWord) (depth : Nat) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability List.BinaryPrefix.rawLastBit =
      1 / 2 := by
  have factorization :=
    rawExtensionDistribution_probability_lastTrue_and_parent stem depth
      (fun _ => true)
  have eventEqual :
      (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability
          (fun word => List.BinaryPrefix.rawLastBit word &&
            (fun _ : CCLMeasureWord => true) (List.BinaryPrefix.rawParent word)) =
        (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability List.BinaryPrefix.rawLastBit :=
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability_congr _ _
      (fun word => Bool.and_true _)
  rw [eventEqual,
    (BinaryPrefix.rawExtensionDistribution stem depth).probability_true,
    mul_one] at factorization
  exact factorization
end Purelib.Measure.BinaryPrefix

end
