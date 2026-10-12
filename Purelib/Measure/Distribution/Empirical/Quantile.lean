module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction

import Purelib.Data.List.Multiplicity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Empirical.Basic
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
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite empirical quantile certificates

Two empirical cumulative frequencies, at explicitly supplied lower and upper
cuts, certify a bracket for an executable empirical lower quantile.  A shared
finite sampling request controls those cuts together with any other displayed
thresholds.  There is no infinite empirical process and no convergence of a
sequence of quantiles.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Compute the lower quantile of a nonempty empirical sample law, returning zero for an empty sample. -/
def sampleLowerQuantile (samples : List Fraction.Rational)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) : Fraction.Rational :=
  if positiveLength : 0 < samples.length then
    (empiricalDistribution samples positiveLength).lowerQuantile
      level levelPositive levelAtMostOne
  else 0

/-- On the exact nonempty sample list, the total sample-quantile function equals its empirical law's lower quantile. -/
theorem sampleLowerQuantile_eq_of_positive
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    sampleLowerQuantile samples level levelPositive levelAtMostOne =
      (empiricalDistribution samples positiveLength).lowerQuantile
        level levelPositive levelAtMostOne := by
  unfold sampleLowerQuantile
  rw [dif_pos positiveLength]

end

open Purelib in
open Purelib.Data.Rat in
/-- The computed lower quantile of a nonempty original sample occurs in that exact sample list. -/
theorem sampleLowerQuantile_sampleContains
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Data.List.SampleContains
      (sampleLowerQuantile samples level levelPositive levelAtMostOne)
      samples := by
  have quantileEqual := sampleLowerQuantile_eq_of_positive samples
    positiveLength level levelPositive levelAtMostOne
  rcases (empiricalDistribution samples positiveLength)
      |>.lowerQuantile_eq_atom_of_mem level levelPositive levelAtMostOne with
    ⟨atom, member, valueEqual⟩
  have contains := empiricalDistribution_atom_sampleContains samples
    positiveLength atom member
  rw [quantileEqual]
  simpa only [valueEqual] using contains

open Purelib.Data.Rat
/-- Select samples of the requested length whose lower quantile escapes the interval open at the lower endpoint and
closed at the upper endpoint. -/
def empiricalLowerQuantileBracketDeviation
    (count : Nat) (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (lower upper : Fraction.Rational) :
    List Fraction.Rational → Bool :=
  fun samples => decide
    (samples.length = count ∧
      (sampleLowerQuantile samples level levelPositive levelAtMostOne ≤ lower ∨
        upper < sampleLowerQuantile samples level levelPositive
          levelAtMostOne))

/-- Read the exact lower-quantile bracket deviation event at level one half. -/
def empiricalMedianBracketDeviation
    (count : Nat) (lower upper : Fraction.Rational) : List Fraction.Rational → Bool :=
  empiricalLowerQuantileBracketDeviation count (1 / 2)
    (by decide) (by decide) lower upper
end Distribution

end Purelib.Measure

end
