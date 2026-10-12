module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
public import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
public section

/-!
# Constructive finite rational quantiles

A rational-valued finite distribution admits an executable lower quantile at
every displayed level in `(0, 1]`.  The implementation insertion-sorts the
displayed atom table and performs a terminating weighted crossing search.
The result is accompanied by the exact strict-lower and cumulative
inequalities; no infimum, completed real line, or choice principle occurs.
-/

namespace Purelib.Measure

section
open Purelib
open Purelib.Data.Rat
/-- Compute the original finite distribution's quantile certificate at level one half. -/
@[expose] def Distribution.medianCertificate
    (distribution : Measure.Distribution Fraction.Rational) :
    QuantileCertificate distribution (1 / 2) :=
  distribution.quantileCertificate (1 / 2) (by decide) (by decide)

/-- Read the exact lower quantile at level one half as the finite distribution's median. -/
@[expose] def Distribution.median
    (distribution : Measure.Distribution Fraction.Rational) : Fraction.Rational :=
  distribution.lowerQuantile (1 / 2) (by decide) (by decide)

/-- Original probability strictly below the computed median is less than one half. -/
theorem Distribution.probability_strictlyBelow_median_lt_half
    (distribution : Measure.Distribution Fraction.Rational) :
    distribution.probability (strictlyBelowEvent distribution.median) < 1 / 2 :=
  distribution.medianCertificate.probability_strictlyBelow_lt

/-- Original cumulative probability at the computed median is at least one half. -/
theorem Distribution.half_le_cumulative_median
    (distribution : Measure.Distribution Fraction.Rational) :
    1 / 2 ≤ distribution.cumulative distribution.median :=
  distribution.medianCertificate.level_le_cumulative

/-- Original probability at or above the computed lower median is strictly greater than one half. -/
theorem Distribution.half_lt_probability_atLeast_median
    (distribution : Measure.Distribution Fraction.Rational) :
    1 / 2 < distribution.probability
      (atLeastCoordinateEvent distribution.median) := by
  have sum := distribution.probability_add_complement
    (strictlyBelowEvent distribution.median)
  have complementProbability := distribution.probability_congr
    (complementEvent (strictlyBelowEvent distribution.median))
    (atLeastCoordinateEvent distribution.median)
    (Measure.complement_strictlyBelowEvent distribution.median)
  rw [complementProbability] at sum
  apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
  intro upperLeHalf
  have sumLt :
      distribution.probability (strictlyBelowEvent distribution.median) +
          distribution.probability
            (atLeastCoordinateEvent distribution.median) < 1 := by
    calc
      distribution.probability (strictlyBelowEvent distribution.median) +
            distribution.probability
              (atLeastCoordinateEvent distribution.median) ≤
          distribution.probability
              (strictlyBelowEvent distribution.median) + 1 / 2 :=
        Fraction.Order.Arithmetic.add_le_add_direct le_rfl upperLeHalf
      _ < 1 / 2 + 1 / 2 :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          distribution.probability_strictlyBelow_median_lt_half (1 / 2)
      _ = 1 := by decide
  rw [sum] at sumLt
  exact sumLt.2 le_rfl

end

end Purelib.Measure

end
