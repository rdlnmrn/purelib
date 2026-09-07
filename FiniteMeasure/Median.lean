import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Quantile
import FiniteMeasure.L1

/-!
# Finite medians minimize rational absolute deviation

The executable lower median supplied by `FiniteMeasure.Quantile` minimizes
the exact expected rational separation from a constant.  The proof uses the
two displayed median event masses and finite expectation monotonicity; no
convex-analysis existence theorem or completed function space occurs.
-/

namespace FiniteMeasure

theorem rationalSeparation_eq_right_sub_of_le
    {left right : Coordinate} (order : left ≤ right) :
    rationalSeparation left right = right - left := by
  unfold rationalSeparation
  apply max_eq_right
  calc
    left - right ≤ right - right :=
      RFAP.ConstructiveFraction.sub_le_sub_right_direct order right
    _ = 0 := by ring1
    _ ≤ right - left :=
      RFAP.ConstructiveFraction.sub_nonneg_direct order

theorem rationalSeparation_eq_left_sub_of_le
    {left right : Coordinate} (order : right ≤ left) :
    rationalSeparation left right = left - right := by
  rw [rationalSeparation_symm,
    rationalSeparation_eq_right_sub_of_le order]

namespace Distribution

/-- Exact expected rational absolute deviation from a displayed centre. -/
def absoluteDeviation (distribution : Distribution Coordinate)
    (center : Coordinate) : Coordinate :=
  distribution.expectation fun value => rationalSeparation value center

private theorem lowerMedianSlope_le_difference
    {candidate median value : Coordinate} (candidateLe : candidate ≤ median) :
    (median - candidate) *
        (1 - 2 * indicator (strictlyBelowEvent median) value) ≤
      rationalSeparation value candidate -
        rationalSeparation value median := by
  by_cases below : value < median
  · have triangle := rationalSeparation_triangle value candidate median
    rw [rationalSeparation_eq_right_sub_of_le candidateLe] at triangle
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct triangle
      (-rationalSeparation value median - (median - candidate))
    simp only [indicator, strictlyBelowEvent, below, decide_true]
    calc
      (median - candidate) * (1 - 2 * 1) = -(median - candidate) := by
        ring1
      _ = rationalSeparation value median +
          (-rationalSeparation value median - (median - candidate)) := by
        ring1
      _ ≤ (rationalSeparation value candidate + (median - candidate)) +
          (-rationalSeparation value median - (median - candidate)) :=
        shifted
      _ = rationalSeparation value candidate -
          rationalSeparation value median := by ring1
  · have medianLeValue : median ≤ value :=
      RFAP.ConstructiveFraction.le_of_not_gt_direct below
    have candidateLeValue := candidateLe.trans medianLeValue
    simp only [indicator, strictlyBelowEvent, below, decide_false,
      rationalSeparation_eq_left_sub_of_le candidateLeValue,
      rationalSeparation_eq_left_sub_of_le medianLeValue]
    apply le_of_eq
    ring1

private theorem upperMedianSlope_le_difference
    {candidate median value : Coordinate} (medianLe : median ≤ candidate) :
    (candidate - median) *
        (2 * indicator (atMostEvent median) value - 1) ≤
      rationalSeparation value candidate -
        rationalSeparation value median := by
  by_cases atMost : value ≤ median
  · have valueLeCandidate := atMost.trans medianLe
    simp only [indicator, atMostEvent, atMost, decide_true,
      rationalSeparation_eq_right_sub_of_le valueLeCandidate,
      rationalSeparation_eq_right_sub_of_le atMost]
    apply le_of_eq
    ring1
  · have triangle := rationalSeparation_triangle value candidate median
    rw [rationalSeparation_eq_left_sub_of_le medianLe] at triangle
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct triangle
      (-rationalSeparation value median - (candidate - median))
    simp only [indicator, atMostEvent, atMost, decide_false]
    calc
      (candidate - median) * (2 * 0 - 1) = -(candidate - median) := by
        ring1
      _ = rationalSeparation value median +
          (-rationalSeparation value median - (candidate - median)) := by
        ring1
      _ ≤ (rationalSeparation value candidate + (candidate - median)) +
          (-rationalSeparation value median - (candidate - median)) :=
        shifted
      _ = rationalSeparation value candidate -
          rationalSeparation value median := by ring1

/-- Every certified finite median minimizes exact expected rational absolute
deviation among all rational centres. -/
theorem absoluteDeviation_le_of_quantileCertificate
    {distribution : Distribution Coordinate}
    (certificate : QuantileCertificate distribution (1 / 2))
    (candidate : Coordinate) :
    distribution.absoluteDeviation certificate.threshold ≤
      distribution.absoluteDeviation candidate := by
  rcases le_total candidate certificate.threshold with candidateLe | medianLe
  · let delta := certificate.threshold - candidate
    let event := strictlyBelowEvent certificate.threshold
    have doubledLess :
        2 * distribution.probability event < 1 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide : (0 : Coordinate) < 2)
          certificate.probability_strictlyBelow_lt
      have twoHalves : (2 : Coordinate) * (1 / 2) = 1 := by decide
      rw [twoHalves] at scaled
      exact scaled
    have slopePositive :
        0 < 1 - 2 * distribution.probability event :=
      RFAP.ConstructiveFraction.sub_pos_direct doubledLess
    have deltaNonnegative : 0 ≤ delta :=
      RFAP.ConstructiveFraction.sub_nonneg_direct candidateLe
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
      exact RFAP.ConstructiveFraction.mul_nonneg_direct deltaNonnegative
        (RFAP.ConstructiveFraction.le_of_lt_direct slopePositive)
    have averaged := distribution.expectation_mono
      (fun value => delta * (1 - 2 * indicator event value))
      (fun value => rationalSeparation value candidate -
        rationalSeparation value certificate.threshold)
      (fun atom member => lowerMedianSlope_le_difference candidateLe)
    have differenceNonnegative := lowerNonnegative.trans averaged
    rw [distribution.expectation_sub] at differenceNonnegative
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      differenceNonnegative
  · let delta := candidate - certificate.threshold
    let event := atMostEvent certificate.threshold
    have doubledAtLeast :
        1 ≤ 2 * distribution.probability event := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          certificate.level_le_cumulative (by decide : (0 : Coordinate) ≤ 2)
      have twoHalves : (2 : Coordinate) * (1 / 2) = 1 := by decide
      rw [twoHalves] at scaled
      exact scaled
    have slopeNonnegative :
        0 ≤ 2 * distribution.probability event - 1 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct doubledAtLeast
    have deltaNonnegative : 0 ≤ delta :=
      RFAP.ConstructiveFraction.sub_nonneg_direct medianLe
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
      exact RFAP.ConstructiveFraction.mul_nonneg_direct deltaNonnegative
        slopeNonnegative
    have averaged := distribution.expectation_mono
      (fun value => delta * (2 * indicator event value - 1))
      (fun value => rationalSeparation value candidate -
        rationalSeparation value certificate.threshold)
      (fun atom member => upperMedianSlope_le_difference medianLe)
    have differenceNonnegative := lowerNonnegative.trans averaged
    rw [distribution.expectation_sub] at differenceNonnegative
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      differenceNonnegative

theorem medianCertificate_threshold
    (distribution : Distribution Coordinate) :
    distribution.medianCertificate.threshold = distribution.median := rfl

/-- The executable lower median is a best rational constant in finite L1. -/
theorem absoluteDeviation_median_le
    (distribution : Distribution Coordinate) (candidate : Coordinate) :
    distribution.absoluteDeviation distribution.median ≤
      distribution.absoluteDeviation candidate := by
  rw [← distribution.medianCertificate_threshold]
  exact absoluteDeviation_le_of_quantileCertificate
    distribution.medianCertificate candidate

end Distribution

end FiniteMeasure
