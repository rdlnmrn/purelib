module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Moments.Basic
public import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.Moments
public import Purelib.Measure.Sampling.Statistic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Explicit finite repeated sampling

An `iidSamples` table contains lists of exactly a supplied natural number of
draws from one displayed rational distribution.  The construction uses only
finite products and pushforwards.  Sample sums and means then have exact
rational expectation and variance formulas, giving a one-shot finite
Chebyshev estimate with the familiar reciprocal sample-count factor.

No infinite product, sequence of random variables, or asymptotic law is
constructed.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat
/-- Decide whether the exact sample mean's squared deviation from the original expectation reaches the squared
threshold. -/
def sampleMeanDeviation {α : Type} (source : Distribution α)
    (count : Nat) (value : α → Fraction.Rational) (threshold : Fraction.Rational) :
    List α → Bool :=
  fun sample => decide
    (threshold ^ 2 ≤
      (sampleMean count value sample - source.expectation value) ^ 2)

/-- The exact sample-mean deviation probability is at most original variance divided by draw count and threshold
squared.

The draw count and threshold must both be positive; the probability is computed under the original independent-sample
law. -/
theorem iidSamples_sampleMean_chebyshev {α : Type}
    (source : Distribution α) (value : α → Fraction.Rational)
    (count : Nat) (countPositive : 0 < (count : Fraction.Rational))
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold) :
    (iidSamples source count).probability
        (sampleMeanDeviation source count value threshold) ≤
      (source.variance value / (count : Fraction.Rational)) / threshold ^ 2 := by
  have estimate := (iidSamples source count).chebyshev_bound
    (sampleMeanDeviation source count value threshold)
    (sampleMean count value) threshold thresholdPositive (by
      intro atom member selected
      rw [source.iidSamples_expectation_sampleMean value count countPositive]
      exact of_decide_eq_true selected)
  rw [source.iidSamples_variance_sampleMean value count countPositive]
    at estimate
  exact estimate

end Distribution

end Purelib.Measure

end
