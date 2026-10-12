module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Measure.BinaryPrefix.Averaging
public import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.BinaryPrefix.Distribution.Consistency
import Purelib.Measure.BinaryPrefix.Distribution.Variance
public import Purelib.Measure.CCL.Prefix.Content
import Purelib.Measure.Distribution.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

section
@[expose] public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Measure in
/-- The normalized finite law of binary extensions of the exact completed-prefix word.

The supplied depth counts additional binary digits; occurrences and weights come directly from the raw extension
construction. -/
def completedPrefixExtensionDistribution
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) :
    Measure.Distribution CCLMeasureWord :=
  BinaryPrefix.rawExtensionDistribution (Block.Basic.rawWord blocks) depth

open Purelib.Data.CCL.Encoding in
open Purelib.Measure in
/-- The extension law has exactly two to the additional depth atom occurrences. -/
theorem completedPrefixExtensionDistribution_atoms_length
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) :
    (completedPrefixExtensionDistribution blocks depth).atoms.length =
      2 ^ depth :=
  BinaryPrefix.rawExtensionDistribution_atoms_length (Block.Basic.rawWord blocks) depth

section
open Purelib.Data
open Purelib.Data.CCL.Encoding
section
open Purelib.Measure
/-- An extension event's probability is its content weight divided by the original positive prefix weight. -/
theorem completedPrefixExtensionDistribution_probability
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (completedPrefixExtensionDistribution blocks depth).probability event =
      (CCL.Prefix.completedPrefixExtensionContent blocks depth).measure event /
        CCL.Prefix.completedPrefixWeight blocks :=
  BinaryPrefix.rawExtensionDistribution_probability
    (Block.Basic.rawWord blocks) depth event

/-- Pulling an event back along one binary parent preserves its completed-prefix extension probability. -/
theorem completedPrefixExtensionDistribution_probability_parent
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (completedPrefixExtensionDistribution blocks (depth + 1)).probability
        (fun word => event (List.BinaryPrefix.rawParent word)) =
      (completedPrefixExtensionDistribution blocks depth).probability event :=
  BinaryPrefix.rawExtensionDistribution_probability_parent
    (Block.Basic.rawWord blocks) depth event

end

open Purelib.Data.Rat in
open Purelib.Measure in
/-- Pulling an observable back along one binary parent preserves its completed-prefix extension expectation. -/
theorem completedPrefixExtensionDistribution_expectation_parent
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (value : CCLMeasureWord →
      Fraction.Rational) :
    (completedPrefixExtensionDistribution blocks (depth + 1)).expectation
        (fun word => value (List.BinaryPrefix.rawParent word)) =
      (completedPrefixExtensionDistribution blocks depth).expectation value :=
  BinaryPrefix.rawExtensionDistribution_expectation_parent
    (Block.Basic.rawWord blocks) depth value

open Purelib.Measure in
/-- Pulling an event back along the retained extra-depth ancestor preserves extension probability. -/
theorem completedPrefixExtensionDistribution_probability_ancestor
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (event : CCLMeasureWord → Bool)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks (depth + extra)).probability
        (fun word => event (List.BinaryPrefix.rawAncestor extra word)) =
      (completedPrefixExtensionDistribution blocks depth).probability event :=
  BinaryPrefix.rawExtensionDistribution_probability_ancestor
    (Block.Basic.rawWord blocks) depth event extra

open Purelib.Data.Rat
open Purelib.Measure
/-- Pulling an observable back along the retained extra-depth ancestor preserves extension expectation. -/
theorem completedPrefixExtensionDistribution_expectation_ancestor
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (value : CCLMeasureWord → Fraction.Rational)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks (depth + extra)).expectation
        (fun word => value (List.BinaryPrefix.rawAncestor extra word)) =
      (completedPrefixExtensionDistribution blocks depth).expectation value :=
  BinaryPrefix.rawExtensionDistribution_expectation_ancestor
    (Block.Basic.rawWord blocks) depth value extra

/-- Backward averaging over the retained extra depth agrees with expectation under the deeper extension law. -/
theorem completedPrefixExtensionDistribution_expectation_backward
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (value : CCLMeasureWord → Fraction.Rational)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks depth).expectation
        (BinaryPrefix.rawBackwardMean extra value) =
      (completedPrefixExtensionDistribution blocks (depth + extra)).expectation
        value :=
  BinaryPrefix.rawExtensionDistribution_expectation_backward
    (Block.Basic.rawWord blocks) depth value extra

/-- Backward averaging cannot increase variance relative to the corresponding deeper extension law. -/
theorem completedPrefixExtensionDistribution_variance_backward
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (value : CCLMeasureWord → Fraction.Rational)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks depth).variance
        (BinaryPrefix.rawBackwardMean extra value) ≤
      (completedPrefixExtensionDistribution blocks (depth + extra)).variance
        value :=
  BinaryPrefix.rawExtensionDistribution_variance_backward
    (Block.Basic.rawWord blocks) depth value extra

/-- Deeper extension variance splits into expected backward variance and variance of the backward mean. -/
theorem completedPrefixExtensionDistribution_totalVariance_backward
    (blocks : List Data.CCL.Encoding.Block) (depth : Nat) (value : CCLMeasureWord → Fraction.Rational)
    (extra : Nat) :
    (completedPrefixExtensionDistribution blocks (depth + extra)).variance
        value =
      (completedPrefixExtensionDistribution blocks depth).expectation
          (BinaryPrefix.rawBackwardVariance extra value) +
        (completedPrefixExtensionDistribution blocks depth).variance
          (BinaryPrefix.rawBackwardMean extra value) :=
  BinaryPrefix.rawExtensionDistribution_totalVariance_backward
    (Block.Basic.rawWord blocks) depth value extra
end

end Purelib.Measure.CCL.Prefix

end
