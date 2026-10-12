module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Median.Basic
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Measure.Distribution.Stability
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Finite medians minimize rational absolute deviation

The executable lower median supplied by `FiniteMeasure.Quantile` minimizes
the exact expected rational separation from a constant.  The proof uses the
two displayed median event masses and finite expectation monotonicity; no
convex-analysis existence theorem or completed function space occurs.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat
/-- Average rational separation from the supplied center under the exact original distribution. -/
@[expose] def absoluteDeviation (distribution : Distribution Fraction.Rational)
    (center : Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun value => Distance.rationalSeparation value center

/-- For a candidate center at or below the median, the below-median indicator bounds the pointwise increase in absolute
deviation. -/
private theorem lowerMedianSlope_le_difference
    {candidate median value : Fraction.Rational} (candidateLe : candidate ≤ median) :
    (median - candidate) *
        (1 - 2 * indicator (strictlyBelowEvent median) value) ≤
      Distance.rationalSeparation value candidate -
        Distance.rationalSeparation value median := by
  by_cases below : value < median
  · have triangle := Distance.rationalSeparation_triangle value candidate median
    rw [Distance.rationalSeparation_eq_right_sub_of_le candidateLe] at triangle
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct triangle
      (-Distance.rationalSeparation value median - (median - candidate))
    simp only [-eq_self, -iff_self, indicator, strictlyBelowEvent, decide_eq_true below]
    calc
      (median - candidate) * (1 - 2 * 1) = -(median - candidate) := by
        ring1
      _ = Distance.rationalSeparation value median +
          (-Distance.rationalSeparation value median - (median - candidate)) := by
        ring1
      _ ≤ (Distance.rationalSeparation value candidate + (median - candidate)) +
          (-Distance.rationalSeparation value median - (median - candidate)) :=
        shifted
      _ = Distance.rationalSeparation value candidate -
          Distance.rationalSeparation value median := by ring1
  · have medianLeValue : median ≤ value :=
      Fraction.Order.Arithmetic.le_of_not_gt_direct below
    have candidateLeValue := candidateLe.trans medianLeValue
    simp only [-eq_self, -iff_self, indicator, strictlyBelowEvent, decide_eq_false below,
      Distance.rationalSeparation_eq_left_sub_of_le candidateLeValue,
      Distance.rationalSeparation_eq_left_sub_of_le medianLeValue]
    apply le_of_eq
    ring1

/-- For a candidate center at or above the median, the at-most-median indicator bounds the pointwise increase in
absolute deviation. -/
private theorem upperMedianSlope_le_difference
    {candidate median value : Fraction.Rational} (medianLe : median ≤ candidate) :
    (candidate - median) *
        (2 * indicator (atMostEvent median) value - 1) ≤
      Distance.rationalSeparation value candidate -
        Distance.rationalSeparation value median := by
  by_cases atMost : value ≤ median
  · have valueLeCandidate := atMost.trans medianLe
    simp only [-eq_self, -iff_self, indicator, atMostEvent, decide_eq_true atMost,
      Distance.rationalSeparation_eq_right_sub_of_le valueLeCandidate,
      Distance.rationalSeparation_eq_right_sub_of_le atMost]
    apply le_of_eq
    ring1
  · have triangle := Distance.rationalSeparation_triangle value candidate median
    rw [Distance.rationalSeparation_eq_left_sub_of_le medianLe] at triangle
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct triangle
      (-Distance.rationalSeparation value median - (candidate - median))
    simp only [-eq_self, -iff_self, indicator, atMostEvent, decide_eq_false atMost]
    calc
      (candidate - median) * (2 * 0 - 1) = -(candidate - median) := by
        ring1
      _ = Distance.rationalSeparation value median +
          (-Distance.rationalSeparation value median - (candidate - median)) := by
        ring1
      _ ≤ (Distance.rationalSeparation value candidate + (candidate - median)) +
          (-Distance.rationalSeparation value median - (candidate - median)) :=
        shifted
      _ = Distance.rationalSeparation value candidate -
          Distance.rationalSeparation value median := by ring1

/-- A retained level-one-half quantile threshold minimizes original expected absolute deviation among all rational
centers.

Its strict below-threshold and weak at-threshold probability certificates supply the two one-sided comparison
inequalities. -/
theorem absoluteDeviation_le_of_quantileCertificate
    {distribution : Distribution Fraction.Rational}
    (certificate : QuantileCertificate distribution (1 / 2))
    (candidate : Fraction.Rational) :
    distribution.absoluteDeviation certificate.threshold ≤
      distribution.absoluteDeviation candidate := by
  rcases le_total candidate certificate.threshold with candidateLe | medianLe
  · let delta := certificate.threshold - candidate
    let event := strictlyBelowEvent certificate.threshold
    have doubledLess :
        2 * distribution.probability event < 1 := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide : (0 : Fraction.Rational) < 2)
          certificate.probability_strictlyBelow_lt
      have twoHalves : (2 : Fraction.Rational) * (1 / 2) = 1 := by decide
      rw [twoHalves] at scaled
      exact scaled
    have slopePositive :
        0 < 1 - 2 * distribution.probability event :=
      Fraction.Order.Arithmetic.sub_pos_direct doubledLess
    have deltaNonnegative : 0 ≤ delta :=
      Fraction.Order.Arithmetic.sub_nonneg_direct candidateLe
    have lowerExpectation :
        distribution.expectation (fun value =>
            delta * (1 - 2 * indicator event value)) =
          delta * (1 - 2 * distribution.probability event) := by
      rw [distribution.expectation_scale, distribution.expectation_sub,
        distribution.expectation_constant, distribution.expectation_scale,
        distribution.expectation_indicator]
    have lowerNonnegative : 0 ≤
        distribution.expectation (fun value =>
          delta * (1 - 2 * indicator event value)) := by
      rw [lowerExpectation]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct deltaNonnegative
        (Fraction.Order.Arithmetic.le_of_lt_direct slopePositive)
    have averaged := distribution.expectation_mono
      (fun value => delta * (1 - 2 * indicator event value))
      (fun value => Distance.rationalSeparation value candidate -
        Distance.rationalSeparation value certificate.threshold)
      (fun atom member => lowerMedianSlope_le_difference candidateLe)
    have differenceNonnegative := lowerNonnegative.trans averaged
    rw [distribution.expectation_sub] at differenceNonnegative
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      differenceNonnegative
  · let delta := candidate - certificate.threshold
    let event := atMostEvent certificate.threshold
    have doubledAtLeast :
        1 ≤ 2 * distribution.probability event := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          certificate.level_le_cumulative (by decide : (0 : Fraction.Rational) ≤ 2)
      have twoHalves : (2 : Fraction.Rational) * (1 / 2) = 1 := by decide
      rw [twoHalves] at scaled
      exact scaled
    have slopeNonnegative :
        0 ≤ 2 * distribution.probability event - 1 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct doubledAtLeast
    have deltaNonnegative : 0 ≤ delta :=
      Fraction.Order.Arithmetic.sub_nonneg_direct medianLe
    have lowerExpectation :
        distribution.expectation (fun value =>
            delta * (2 * indicator event value - 1)) =
          delta * (2 * distribution.probability event - 1) := by
      rw [distribution.expectation_scale, distribution.expectation_sub,
        distribution.expectation_scale, distribution.expectation_indicator,
        distribution.expectation_constant]
    have lowerNonnegative : 0 ≤
        distribution.expectation (fun value =>
          delta * (2 * indicator event value - 1)) := by
      rw [lowerExpectation]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct deltaNonnegative
        slopeNonnegative
    have averaged := distribution.expectation_mono
      (fun value => delta * (2 * indicator event value - 1))
      (fun value => Distance.rationalSeparation value candidate -
        Distance.rationalSeparation value certificate.threshold)
      (fun atom member => upperMedianSlope_le_difference medianLe)
    have differenceNonnegative := lowerNonnegative.trans averaged
    rw [distribution.expectation_sub] at differenceNonnegative
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      differenceNonnegative

/-- The computed median certificate retains exactly the original law's computed lower median. -/
theorem medianCertificate_threshold
    (distribution : Distribution Fraction.Rational) :
    distribution.medianCertificate.threshold = distribution.median := rfl

/-- The exact computed lower median minimizes original expected absolute deviation among rational centers. -/
theorem absoluteDeviation_median_le
    (distribution : Distribution Fraction.Rational) (candidate : Fraction.Rational) :
    distribution.absoluteDeviation distribution.median ≤
      distribution.absoluteDeviation candidate := by
  rw [← distribution.medianCertificate_threshold]
  exact absoluteDeviation_le_of_quantileCertificate
    distribution.medianCertificate candidate

end Distribution

end Purelib.Measure

end
