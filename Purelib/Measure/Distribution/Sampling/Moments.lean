module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Product.Expectation
import Purelib.Measure.Distribution.Product.Moments
import Purelib.Measure.Distribution.Pure.Moments
import Purelib.Measure.Distribution.Pushforward.Moments
public import Purelib.Measure.Distribution.Sampling.Basic
public import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Event
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.NatCast.Reciprocal
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
public section

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

open Purelib.Algebra
namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- The exact independent sample sum has expectation equal to draw count times the original expectation. -/
theorem iidSamples_expectation_sampleSum {α : Type}
    (source : Measure.Distribution α) (value : α → Fraction.Rational) :
    ∀ count : Nat,
      (iidSamples source count).expectation (sampleSum value) =
        (count : Fraction.Rational) * source.expectation value
  | 0 => by
      rw [iidSamples_zero, Distribution.pure_expectation]
      simp only [-eq_self, -iff_self, sampleSum, Nat.cast_zero, zero_mul]
      rfl
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_expectation]
      change
        (source.product (iidSamples source count)).expectation
            (fun pair => value pair.1 + sampleSum value pair.2) =
          ((count + 1 : Nat) : Fraction.Rational) * source.expectation value
      rw [(source.product (iidSamples source count)).expectation_add,
        source.product_expectation_left,
        source.product_expectation_right,
        iidSamples_expectation_sampleSum source value count,
        NatCast.add, Nat.cast_one]
      ring1

/-- The exact independent sample sum has variance equal to draw count times the original variance. -/
theorem iidSamples_variance_sampleSum {α : Type}
    (source : Measure.Distribution α) (value : α → Fraction.Rational) :
    ∀ count : Nat,
      (iidSamples source count).variance (sampleSum value) =
        (count : Fraction.Rational) * source.variance value
  | 0 => by
      rw [iidSamples_zero, Distribution.pure_variance]
      simp only [-eq_self, -iff_self, Nat.cast_zero, zero_mul]
      rfl
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_variance]
      change
        (source.product (iidSamples source count)).variance
            (fun pair => value pair.1 + sampleSum value pair.2) =
          ((count + 1 : Nat) : Fraction.Rational) * source.variance value
      rw [source.product_variance_add_coordinates,
        iidSamples_variance_sampleSum source value count,
        NatCast.add, Nat.cast_one]
      ring1

/-- At positive draw count, the exact sample mean has the original source expectation. -/
theorem iidSamples_expectation_sampleMean {α : Type}
    (source : Measure.Distribution α) (value : α → Fraction.Rational)
    (count : Nat) (positive : 0 < (count : Fraction.Rational)) :
    (iidSamples source count).expectation (sampleMean count value) =
      source.expectation value := by
  unfold sampleMean
  rw [source.iidSamples count |>.expectation_scale,
    iidSamples_expectation_sampleSum]
  exact positiveSampleCount_inv_mul_value count positive
    (source.expectation value)

/-- At positive draw count, exact sample-mean variance equals original variance divided by draw count. -/
theorem iidSamples_variance_sampleMean {α : Type}
    (source : Measure.Distribution α) (value : α → Fraction.Rational)
    (count : Nat) (positive : 0 < (count : Fraction.Rational)) :
    (iidSamples source count).variance (sampleMean count value) =
      source.variance value / (count : Fraction.Rational) := by
  unfold sampleMean
  rw [(iidSamples source count).variance_scale,
    iidSamples_variance_sampleSum]
  exact positiveSampleCount_inv_sq_mul_value count positive
    (source.variance value)

/-- At positive draw count, expected empirical event frequency equals the original event probability. -/
theorem iidSamples_expectation_eventFrequency {α : Type}
    (source : Measure.Distribution α) (event : α → Bool)
    (count : Nat) (positive : 0 < (count : Fraction.Rational)) :
    (iidSamples source count).expectation (eventFrequency count event) =
      source.probability event := by
  unfold eventFrequency
  rw [source.iidSamples_expectation_sampleMean
    (indicator event) count positive, source.expectation_indicator]

/-- At positive draw count, empirical event-frequency variance is original probability times its complement divided by
draw count. -/
theorem iidSamples_variance_eventFrequency {α : Type}
    (source : Measure.Distribution α) (event : α → Bool)
    (count : Nat) (positive : 0 < (count : Fraction.Rational)) :
    (iidSamples source count).variance (eventFrequency count event) =
      (source.probability event * (1 - source.probability event)) /
        (count : Fraction.Rational) := by
  unfold eventFrequency
  rw [source.iidSamples_variance_sampleMean
    (indicator event) count positive, source.variance_indicator]
end

end Distribution

end Purelib.Measure

end
