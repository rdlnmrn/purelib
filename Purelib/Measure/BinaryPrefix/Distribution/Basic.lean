module
import Purelib.Algebra.Semiring.Nat
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.List.BinaryPrefix.Frontier
import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.BinaryPrefix.Content
public import Purelib.Measure.Content.Normalization.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Event

import Purelib.Tactic.QuotientFreeOmega
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
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

open Purelib.Data.List

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
open Purelib.Measure in
/-- Normalize the exact fixed-depth extension content by the positive original stem weight.

The resulting distribution retains the complete ordered extension frontier and scales its original dyadic weights to
total one. -/
@[expose] def rawExtensionDistribution (stem : CCLMeasureWord)
  (depth : Nat) :
    Measure.Distribution CCLMeasureWord :=
  (BinaryPrefix.rawExtensionContent stem depth).normalize (by
    rw [BinaryPrefix.rawExtensionContent_total]
    exact List.BinaryPrefix.rawPrefixWeight_pos stem)

section
open Purelib.Data
open Purelib.Measure
/-- The normalized extension distribution retains exactly two raised to the depth atoms. -/
theorem rawExtensionDistribution_atoms_length (stem :
  CCLMeasureWord) (depth : Nat) :
    (rawExtensionDistribution stem depth).atoms.length = 2 ^ depth := by
  rw [rawExtensionDistribution,
    Content.normalize_atoms_length]
  simp only [-eq_self, -iff_self, BinaryPrefix.rawExtensionContent, BinaryPrefix.rawPrefixContent, Map.length_map,
    List.BinaryPrefix.rawExtensions_length]; try rfl

/-- An extension event has probability equal to its original extension-content mass divided by the stem weight. -/
theorem rawExtensionDistribution_probability
    (stem : CCLMeasureWord) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (rawExtensionDistribution stem depth).probability event =
      (BinaryPrefix.rawExtensionContent stem depth).measure event /
        List.BinaryPrefix.rawPrefixWeight stem := by
  unfold rawExtensionDistribution
  rw [Content.normalize_probability,
    BinaryPrefix.rawExtensionContent_total]

end

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- An extension event has probability equal to its selected occurrence count times one half raised to the depth. -/
theorem rawExtensionDistribution_probability_eq_count_mul
    (stem : CCLMeasureWord) (depth : Nat) (event : CCLMeasureWord → Bool) :
    (rawExtensionDistribution stem depth).probability event =
      (Data.List.rawFrontierEventCount (List.BinaryPrefix.rawExtensions stem depth) event : Fraction.Rational) *
        (1 / 2 : Fraction.Rational) ^ depth := by
  rw [rawExtensionDistribution_probability]
  change Measure.eventWeight
      ((List.BinaryPrefix.rawExtensions stem depth).map BinaryPrefix.rawPrefixAtom) event /
        List.BinaryPrefix.rawPrefixWeight stem = _
  rw [BinaryPrefix.eventWeight_map_rawPrefixAtom_eq_count_mul
    (List.BinaryPrefix.rawExtensions stem depth) event
    (List.BinaryPrefix.rawPrefixWeight stem * (1 / 2 : Fraction.Rational) ^ depth) (by
      intro word member
      exact BinaryPrefix.rawExtensions_member_weight stem depth word member)]
  apply Fraction.Field.mul_right_cancel_of_ne
    (List.BinaryPrefix.rawPrefixWeight_pos stem).ne'
  calc
    ((Data.List.rawFrontierEventCount (List.BinaryPrefix.rawExtensions stem depth) event : Fraction.Rational) *
          (List.BinaryPrefix.rawPrefixWeight stem * (1 / 2 : Fraction.Rational) ^ depth) /
        List.BinaryPrefix.rawPrefixWeight stem) * List.BinaryPrefix.rawPrefixWeight stem =
      (Data.List.rawFrontierEventCount (List.BinaryPrefix.rawExtensions stem depth) event : Fraction.Rational) *
        (List.BinaryPrefix.rawPrefixWeight stem * (1 / 2 : Fraction.Rational) ^ depth) :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        (List.BinaryPrefix.rawPrefixWeight_pos stem).ne'
    _ = ((Data.List.rawFrontierEventCount
          (List.BinaryPrefix.rawExtensions stem depth) event : Fraction.Rational) *
        (1 / 2 : Fraction.Rational) ^ depth) * List.BinaryPrefix.rawPrefixWeight stem := by ring1

open Purelib in
open Purelib.Data in
open Purelib.Measure in
/-- Retain all words of the specified length with their dyadic prefix weights, already summing to one. -/
@[expose] def fairDepthDistribution (depth : Nat) :
    Measure.Distribution CCLMeasureWord where
  atoms := (List.BinaryPrefix.rawExtensions [] depth).map BinaryPrefix.rawPrefixAtom
  total_one := by
    change (BinaryPrefix.rawExtensionContent [] depth).total = 1
    rw [BinaryPrefix.rawExtensionContent_total, List.BinaryPrefix.rawPrefixWeight_nil]

open Purelib.Data in
open Purelib.Measure in
/-- The fair fixed-depth distribution contains exactly two raised to the depth atoms. -/
theorem fairDepthDistribution_atoms_length (depth : Nat) :
    (fairDepthDistribution depth).atoms.length = 2 ^ depth := by
  simp only [-eq_self, -iff_self, fairDepthDistribution, Map.length_map,
    List.BinaryPrefix.rawExtensions_length]; try rfl

end Purelib.Measure.BinaryPrefix

end
