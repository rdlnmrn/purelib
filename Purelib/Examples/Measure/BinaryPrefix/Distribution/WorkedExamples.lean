module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.RawParser.Truncation
public import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.List.BinaryPrefix.Frontier
import Purelib.Data.List.BinaryPrefix.Truncation
import Purelib.Data.List.Event
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.BinaryPrefix.Averaging
import Purelib.Measure.BinaryPrefix.Content
import Purelib.Measure.BinaryPrefix.Coupling
import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.BinaryPrefix.Distribution.Consistency
import Purelib.Measure.BinaryPrefix.Distribution.Independence
import Purelib.Measure.BinaryPrefix.Distribution.Variance
import Purelib.Measure.CCL.Truncation.Basic
import Purelib.Measure.CCL.Truncation.Moments

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.BinaryPrefix.Distribution.WorkedExamples

open Purelib.Measure
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Geometry.Projective
open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)
open Purelib
open Purelib.Data.Rat
open Purelib.Examples

/-- The Boolean event that a raw binary word has a true third bit. -/
def thirdRawBitTrue :
  CCLMeasureWord → Bool
  | _ :: _ :: true :: _ => true
  | _ => false

/-- Count true bits in a finite raw word as a canonical rational. -/
def rawTrueCount :
  CCLMeasureWord → Fraction.Rational
  | [] => 0
  | bit :: remaining =>
      (if bit then 1 else 0) + rawTrueCount remaining

/-- Three extensions of the displayed two-bit prefix give eight distribution atoms. -/
example :
    (BinaryPrefix.rawExtensionDistribution [true, false] 3).atoms.length =
      8 := by
  decide

/-- The displayed prefix-extension law assigns probability one half to a true third bit. -/
example :
    (BinaryPrefix.rawExtensionDistribution [true, false] 3).probability
      thirdRawBitTrue = 1 / 2 := by
  decide

/-- The normalized extension probability equals raw content mass divided by the original prefix weight. -/
example (stem : CCLMeasureWord) (depth : Nat)
    (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution stem depth).probability event =
      (BinaryPrefix.rawExtensionContent stem depth).measure event /
        List.BinaryPrefix.rawPrefixWeight stem :=
  BinaryPrefix.rawExtensionDistribution_probability stem depth event

/-- Every raw extension event probability equals its finite event count times the depth dyadic weight. -/
example (stem : CCLMeasureWord) (depth : Nat)
    (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution stem depth).probability event =
      (List.rawFrontierEventCount
          (List.BinaryPrefix.rawExtensions stem depth) event : Fraction.Rational) *
        (1 / 2 : Fraction.Rational) ^ depth :=
  BinaryPrefix.rawExtensionDistribution_probability_eq_count_mul
    stem depth event

/-- A raw truncation event probability equals its finite preimage count times the depth dyadic weight. -/
example (stem : CCLMeasureWord) (depth : Nat)
    (event : Line.GaussianLine → Bool) :
    (CCL.Truncation.rawTruncationDistribution stem depth).probability event =
      (List.rawFrontierEventCount
          (List.BinaryPrefix.rawExtensions stem depth)
          (fun word => event (RawParser.rawTruncation word)) :
        Fraction.Rational) * (1 / 2 : Fraction.Rational) ^ depth :=
  CCL.Truncation.rawTruncationDistribution_probability_eq_count_mul
    stem depth event

/-- Raw truncation variance splits into expected backward variance and variance of the backward mean. -/
example (stem : CCLMeasureWord) (depth extra : Nat)
    (probe : Line.GaussianLine → Fraction.Rational) :
    (CCL.Truncation.rawTruncationDistribution
        stem (depth + extra)).variance probe =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
          (BinaryPrefix.rawBackwardVariance extra
            (fun word => probe (RawParser.rawTruncation word))) +
        (BinaryPrefix.rawExtensionDistribution stem depth).variance
          (BinaryPrefix.rawBackwardMean extra
            (fun word => probe (RawParser.rawTruncation word))) :=
  CCL.Truncation.rawTruncationDistribution_totalVariance_backward
    stem depth extra probe

/-- Parent pullback preserves event probability between consecutive raw extension depths. -/
example (stem : CCLMeasureWord) (depth : Nat)
    (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability
        (fun word => event (List.BinaryPrefix.rawParent word)) =
      (BinaryPrefix.rawExtensionDistribution stem depth).probability
        event :=
  BinaryPrefix.rawExtensionDistribution_probability_parent
    stem depth event

/-- The last true bit and a pulled-back parent event have joint probability one half times the parent probability. -/
example (stem : CCLMeasureWord) (depth : Nat)
    (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability
        (fun word => List.BinaryPrefix.rawLastBit word &&
          event (List.BinaryPrefix.rawParent word)) =
      (1 / 2 : Fraction.Rational) *
        (BinaryPrefix.rawExtensionDistribution stem depth).probability
          event :=
  BinaryPrefix.rawExtensionDistribution_probability_lastTrue_and_parent
    stem depth event

/-- The last bit of every one-step extension law is true with probability one half. -/
example (stem : CCLMeasureWord) (depth : Nat) :
    (BinaryPrefix.rawExtensionDistribution stem (depth + 1)).probability
        List.BinaryPrefix.rawLastBit = 1 / 2 :=
  BinaryPrefix.rawExtensionDistribution_probability_lastBit_true
    stem depth

/-- Backward averaging preserves expectation across finite raw extension depths. -/
example (stem : CCLMeasureWord) (depth extra : Nat)
    (value : CCLMeasureWord → Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem depth).expectation
        (BinaryPrefix.rawBackwardMean extra value) =
      (BinaryPrefix.rawExtensionDistribution
        stem (depth + extra)).expectation value :=
  BinaryPrefix.rawExtensionDistribution_expectation_backward
    stem depth value extra

/-- The backward mean of the three-bit true count has expectation three halves. -/
example :
    (BinaryPrefix.rawExtensionDistribution [] 1).expectation
        (BinaryPrefix.rawBackwardMean 2 rawTrueCount) =
          3 / 2 := open Purelib.Measure in by
  rw [BinaryPrefix.rawExtensionDistribution_expectation_backward]
  decide

/-- The one-bit law of the backward true-count mean has variance one quarter. -/
example :
    (BinaryPrefix.rawExtensionDistribution [] 1).variance
        (BinaryPrefix.rawBackwardMean 2 rawTrueCount) =
          1 / 4 := by
  decide

/-- The three-bit true-count observable has variance three quarters. -/
example :
    (BinaryPrefix.rawExtensionDistribution [] 3).variance
        rawTrueCount = 3 / 4 := by
  decide

/-- The expected two-bit backward variance of the true count is one half. -/
example :
    (BinaryPrefix.rawExtensionDistribution [] 1).expectation
        (BinaryPrefix.rawBackwardVariance 2
          rawTrueCount) = 1 / 2 := by
  decide

/-- The displayed total-variance identity is three quarters equals one half plus one quarter. -/
example : (3 / 4 : Fraction.Rational) = 1 / 2 + 1 / 4 := by
  decide

/-- Backward averaging does not increase raw extension variance. -/
example (stem : CCLMeasureWord) (depth extra : Nat)
    (value : CCLMeasureWord → Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution stem depth).variance
        (BinaryPrefix.rawBackwardMean extra value) ≤
      (BinaryPrefix.rawExtensionDistribution
        stem (depth + extra)).variance value :=
  BinaryPrefix.rawExtensionDistribution_variance_backward
    stem depth value extra

/-- The finite raw extension law satisfies the backward total-variance decomposition. -/
example (stem : CCLMeasureWord) (depth extra : Nat)
    (value : CCLMeasureWord → Fraction.Rational) :
    (BinaryPrefix.rawExtensionDistribution
        stem (depth + extra)).variance value =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
          (BinaryPrefix.rawBackwardVariance extra value) +
        (BinaryPrefix.rawExtensionDistribution stem depth).variance
          (BinaryPrefix.rawBackwardMean extra value) :=
  BinaryPrefix.rawExtensionDistribution_totalVariance_backward
    stem depth value extra

/-- Removing the last bit of [true,false,true] gives [true,false]. -/
example : List.BinaryPrefix.rawParent [true, false, true] =
    [true, false] := by
  decide

/-- Removing two final bits of [true,false,true] gives [true]. -/
example : List.BinaryPrefix.rawAncestor 2 [true, false, true] = [true] := by
  decide

/-- Ancestor pullback preserves raw event probability across a finite extra depth. -/
example (stem : CCLMeasureWord) (depth extra : Nat)
    (event : CCLMeasureWord → Bool) :
    (BinaryPrefix.rawExtensionDistribution
        stem (depth + extra)).probability
          (fun word => event (List.BinaryPrefix.rawAncestor extra word)) =
      (BinaryPrefix.rawExtensionDistribution stem depth).probability
        event :=
  BinaryPrefix.rawExtensionDistribution_probability_ancestor
    stem depth event extra

/-- The retained raw ancestor-law coupling has zero mismatch probability. -/
example (stem : CCLMeasureWord) (depth extra : Nat) :
    (BinaryPrefix.rawExtensionAncestorLawCoupling
      stem depth extra).mismatchProbability
        (List.BinaryPrefix.rawAncestorRelation extra) = 0 :=
  BinaryPrefix.rawExtensionAncestorLawCoupling_mismatchProbability
    stem depth extra

/-- The displayed one-to-three-bit ancestor coupling retains eight joint atoms. -/
example : (BinaryPrefix.rawExtensionAncestorLawCoupling [] 1 2).coupling.joint.atoms.length = 8 := by
  decide

/-- Extending the displayed two-bit prefix preserves its content mass one quarter. -/
example :
    (BinaryPrefix.rawExtensionContent [true, false] 4).total = 1 / 4 :=
  BinaryPrefix.rawExtensionContent_total [true, false] 4

/-- The fair three-bit distribution has eight atoms. -/
example : (BinaryPrefix.fairDepthDistribution 3).atoms.length = 8 :=
  BinaryPrefix.fairDepthDistribution_atoms_length 3

/-- The raw-word event that its first bit is true. -/
def startsWithTrue :
  CCLMeasureWord → Bool
  | true :: _ => true
  | _ => false

/-- The fair three-bit law gives probability one half to a true first bit. -/
example : (BinaryPrefix.fairDepthDistribution 3).probability
    startsWithTrue = 1 / 2 := by
  decide

/-- The two child prefix weights add to the original parent prefix weight. -/
example :
    List.BinaryPrefix.rawPrefixWeight [true, false] +
        List.BinaryPrefix.rawPrefixWeight [true, true] =
      List.BinaryPrefix.rawPrefixWeight [true] :=
  List.BinaryPrefix.rawPrefixWeight_children_add [true]

end Purelib.Examples.Measure.BinaryPrefix.Distribution.WorkedExamples

end
