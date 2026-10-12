module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Frontier
import Purelib.Data.List.Event
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.BinaryPrefix.Distribution.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.RawParser.Truncation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

section
@[expose] public section

/-!
# Finite-depth laws of CCL truncation points

The symbolic fair-bit distribution on a displayed raw extension frontier can
be pushed through the parser's explicit projective truncation.  The result is
an ordinary finite distribution of constructive projective points.  No claim
is made about a limiting decoder value or a geometric pushforward measure.
-/

namespace Purelib.Measure.CCL.Truncation

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Map the exact finite binary-extension law through the raw CCL truncation parser.

The supplied stem and additional depth retain all original weighted word occurrences, including equal projective
truncation outputs. -/
def rawTruncationDistribution (stem : CCLMeasureWord) (depth :
  Nat) :
    Measure.Distribution Line.GaussianLine :=
  (BinaryPrefix.rawExtensionDistribution stem depth).map RawParser.rawTruncation

open Purelib.Data in
open Purelib.Measure in
/-- The truncation law retains exactly two to the additional depth atom occurrences. -/
theorem rawTruncationDistribution_atoms_length (stem :
  CCLMeasureWord) (depth : Nat) :
    (rawTruncationDistribution stem depth).atoms.length = 2 ^ depth := by
  rw [rawTruncationDistribution,
    Distribution.map_atoms_length,
    BinaryPrefix.rawExtensionDistribution_atoms_length]

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Truncation-event probability is the exact selected word count times one half to the additional depth. -/
theorem rawTruncationDistribution_probability_eq_count_mul
    (stem : CCLMeasureWord) (depth : Nat)
    (event : Line.GaussianLine → Bool) :
    (rawTruncationDistribution stem depth).probability event =
      (Data.List.rawFrontierEventCount (List.BinaryPrefix.rawExtensions stem depth)
          (fun word => event (RawParser.rawTruncation word)) : Fraction.Rational) *
        (1 / 2 : Fraction.Rational) ^ depth := by
  rw [rawTruncationDistribution,
    Distribution.map_probability,
    BinaryPrefix.rawExtensionDistribution_probability_eq_count_mul]

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Probe expectation under truncation is the original extension expectation of the parsed-word probe. -/
theorem rawTruncationDistribution_expectation
    (stem : CCLMeasureWord) (depth : Nat)
    (probe : Line.GaussianLine → Fraction.Rational) :
    (rawTruncationDistribution stem depth).expectation probe =
      (BinaryPrefix.rawExtensionDistribution stem depth).expectation
        (fun word => probe (RawParser.rawTruncation word)) := by
  rw [rawTruncationDistribution,
    Distribution.map_expectation]
end Purelib.Measure.CCL.Truncation

end
