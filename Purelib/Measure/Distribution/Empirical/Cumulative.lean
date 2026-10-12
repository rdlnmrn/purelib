module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Sampling.Statistic
import Purelib.Data.Rat.Fraction

public import Purelib.Measure.Distribution.Empirical.Basic

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

open Purelib.Data.Rat in
/-- Empirical cumulative probability is the frequency of the exact at-most-threshold event in the original sample list.
-/
theorem empiricalDistribution_cumulative_eq_eventFrequency
    (samples : List Fraction.Rational) (positiveLength : 0 < samples.length)
    (threshold : Fraction.Rational) :
    (empiricalDistribution samples positiveLength).cumulative threshold =
      eventFrequency samples.length (atMostEvent threshold) samples := by
  unfold cumulative
  exact empiricalDistribution_probability_eq_eventFrequency samples
    positiveLength (atMostEvent threshold)
end Distribution

end Purelib.Measure

end
