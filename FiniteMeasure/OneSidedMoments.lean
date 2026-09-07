import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments
import FiniteMeasure.PoweredLp

/-!
# One-sided finite moment inequalities

Cantelli's inequality improves two-sided Chebyshev for a displayed one-sided
deviation event.  The proof below is entirely finite: compare the centered
observable with the event indicator, apply the already finite covariance
Cauchy--Schwarz inequality, and cancel one explicitly positive rational
probability when necessary.
-/

namespace FiniteMeasure

namespace Distribution

/-- Multiplicative form of finite Cantelli inequality.  It avoids division
and remains informative even when the variance is zero. -/
theorem cantelli_mul_probability_le_variance {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate) (threshold : Coordinate)
    (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ value atom.item - distribution.expectation value) :
    (distribution.variance value + threshold ^ 2) *
        distribution.probability event ≤
      distribution.variance value := by
  let centeredIndicator : α → Coordinate := fun item =>
    (value item - distribution.expectation value) * indicator event item
  have centeredIndicator_nonnegative : ∀ atom,
      atom ∈ distribution.atoms → 0 ≤ centeredIndicator atom.item := by
    intro atom atomMember
    cases selected : event atom.item
    · simp only [centeredIndicator, indicator, selected, mul_zero]
      exact le_rfl
    · simp only [centeredIndicator, indicator, selected, mul_one]
      exact positive.le.trans
        (selectedDeviation atom atomMember selected)
  have centeredIndicator_selected : ∀ atom,
      atom ∈ distribution.atoms → event atom.item = true →
        threshold ≤ centeredIndicator atom.item := by
    intro atom atomMember selected
    simp only [centeredIndicator, indicator, selected, mul_one]
    exact selectedDeviation atom atomMember selected
  have thresholdCross :
      threshold * distribution.probability event ≤
        distribution.expectation centeredIndicator :=
    threshold_mul_eventWeight_le_expectationWeight distribution.atoms event
      centeredIndicator threshold centeredIndicator_nonnegative
      centeredIndicator_selected
  have covarianceEq :
      distribution.covariance value (indicator event) =
        distribution.expectation centeredIndicator := by
    calc
      distribution.covariance value (indicator event) =
          distribution.expectation (fun item =>
            value item * indicator event item -
              distribution.expectation value * indicator event item) := by
        rw [distribution.covariance_eq_productMoment_sub_means,
          distribution.expectation_indicator, distribution.expectation_sub,
          distribution.expectation_scale,
          distribution.expectation_indicator]
      _ = distribution.expectation centeredIndicator :=
        distribution.expectation_congr _ _ (fun item => by
          dsimp only [centeredIndicator]
          ring1)
  have thresholdCovariance :
      threshold * distribution.probability event ≤
        distribution.covariance value (indicator event) := by
    rw [covarianceEq]
    exact thresholdCross
  have scaledNonnegative :
      0 ≤ threshold * distribution.probability event :=
    RFAP.ConstructiveFraction.mul_nonneg_direct positive.le
      (distribution.probability_nonneg event)
  have squaredLower :
      (threshold * distribution.probability event) ^ 2 ≤
        distribution.covariance value (indicator event) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct scaledNonnegative
      thresholdCovariance 2
  have indicatorSquare := distribution.expectation_congr
    (fun item => indicator event item ^ 2) (indicator event) (fun item => by
    cases selected : event item <;>
      simp only [indicator, selected] <;> ring1)
  have indicatorVariance :
      distribution.variance (indicator event) =
        distribution.probability event *
          (1 - distribution.probability event) := by
    rw [distribution.variance_eq_secondMoment_sub_sq,
      indicatorSquare, distribution.expectation_indicator]
    ring1
  have covarianceUpper :=
    distribution.covariance_sq_le_variance_mul value (indicator event)
  rw [indicatorVariance] at covarianceUpper
  have combined :
      (threshold * distribution.probability event) ^ 2 ≤
        distribution.variance value *
          (distribution.probability event *
            (1 - distribution.probability event)) :=
    squaredLower.trans covarianceUpper
  by_cases probabilityZero : distribution.probability event = 0
  · rw [probabilityZero, mul_zero]
    exact distribution.variance_nonneg value
  · have probabilityPositive : 0 < distribution.probability event :=
      lt_of_le_of_ne (distribution.probability_nonneg event)
        (Ne.symm probabilityZero)
    have multiplied :
        ((distribution.variance value + threshold ^ 2) *
            distribution.probability event) *
              distribution.probability event ≤
          distribution.variance value * distribution.probability event := by
      calc
        ((distribution.variance value + threshold ^ 2) *
              distribution.probability event) *
            distribution.probability event =
            (threshold * distribution.probability event) ^ 2 +
              distribution.variance value *
                distribution.probability event ^ 2 := by
          ring1
        _ ≤ distribution.variance value *
              (distribution.probability event *
                (1 - distribution.probability event)) +
            distribution.variance value *
              distribution.probability event ^ 2 :=
          add_le_add combined le_rfl
        _ = distribution.variance value *
            distribution.probability event := by
          ring1
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := distribution.probability event)
    · exact multiplied
    · exact probabilityPositive

/-- Divided finite Cantelli inequality. -/
theorem cantelli_bound {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate) (threshold : Coordinate)
    (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ value atom.item - distribution.expectation value) :
    distribution.probability event ≤
      distribution.variance value /
        (distribution.variance value + threshold ^ 2) := by
  have denominatorPositive :
      0 < distribution.variance value + threshold ^ 2 :=
    lt_of_lt_of_le
      (RFAP.ConstructiveFraction.pow_pos_direct positive 2)
      (le_add_of_nonneg_left (distribution.variance_nonneg value))
  apply (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).2
  calc
    distribution.probability event *
          (distribution.variance value + threshold ^ 2) =
        (distribution.variance value + threshold ^ 2) *
          distribution.probability event := by
      ring1
    _ ≤ distribution.variance value :=
      distribution.cantelli_mul_probability_le_variance event value
        threshold positive selectedDeviation

/-- Lower-tail form of finite Cantelli inequality. -/
theorem cantelli_lower_bound {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate) (threshold : Coordinate)
    (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ distribution.expectation value - value atom.item) :
    distribution.probability event ≤
      distribution.variance value /
        (distribution.variance value + threshold ^ 2) := by
  let negated : α → Coordinate := fun item => -value item
  have negatedMean : distribution.expectation negated =
      -distribution.expectation value := by
    calc
      distribution.expectation negated =
          distribution.expectation (fun item =>
            (-1 : Coordinate) * value item) :=
        distribution.expectation_congr _ _ (fun item => by
          dsimp only [negated]
          ring1)
      _ = (-1 : Coordinate) * distribution.expectation value :=
        distribution.expectation_scale (-1) value
      _ = -distribution.expectation value := by ring1
  have selectedNegated : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ≤ negated atom.item - distribution.expectation negated := by
    intro atom atomMember selected
    rw [negatedMean]
    dsimp only [negated]
    have lower := selectedDeviation atom atomMember selected
    calc
      threshold ≤ distribution.expectation value - value atom.item := lower
      _ = -value atom.item - -distribution.expectation value := by
        ring1
  have upper := distribution.cantelli_bound event negated threshold positive
    selectedNegated
  have negatedVariance : distribution.variance negated =
      distribution.variance value := by
    calc
      distribution.variance negated =
          distribution.variance (fun item =>
            (-1 : Coordinate) * value item) :=
        distribution.variance_congr _ _ (fun item => by
          dsimp only [negated]
          ring1)
      _ = (-1 : Coordinate) ^ 2 * distribution.variance value :=
        distribution.variance_scale (-1) value
      _ = distribution.variance value := by ring1
  rw [negatedVariance] at upper
  exact upper

/-- Multiplicative Paley--Zygmund inequality for an explicitly supplied
strict upper event. -/
theorem paleyZygmund_mul {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate) (fraction : Coordinate)
    (fractionNonnegative : 0 ≤ fraction) (fractionAtMostOne : fraction ≤ 1)
    (valueNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (outsideUpper : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = false →
        value atom.item ≤ fraction * distribution.expectation value) :
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 ≤
      distribution.expectation (fun item => value item ^ 2) *
        distribution.probability event := by
  let selectedValue : α → Coordinate := fun item =>
    value item * indicator event item
  have meanNonnegative : 0 ≤ distribution.expectation value :=
    distribution.expectation_nonneg value valueNonnegative
  have fractionMeanNonnegative :
      0 ≤ fraction * distribution.expectation value :=
    RFAP.ConstructiveFraction.mul_nonneg_direct fractionNonnegative
      meanNonnegative
  have pointwise : ∀ atom, atom ∈ distribution.atoms →
      value atom.item ≤ selectedValue atom.item +
        fraction * distribution.expectation value := by
    intro atom atomMember
    cases selected : event atom.item
    · simp only [selectedValue, indicator, selected, mul_zero, zero_add]
      exact outsideUpper atom atomMember selected
    · simp only [selectedValue, indicator, selected, mul_one]
      exact le_add_of_nonneg_right fractionMeanNonnegative
  have averaged := distribution.expectation_mono value
    (fun item => selectedValue item +
      fraction * distribution.expectation value) pointwise
  rw [distribution.expectation_add,
    distribution.expectation_constant] at averaged
  have selectedLower :
      (1 - fraction) * distribution.expectation value ≤
        distribution.expectation selectedValue := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct averaged
      (fraction * distribution.expectation value)
    calc
      (1 - fraction) * distribution.expectation value =
          distribution.expectation value -
            fraction * distribution.expectation value := by
        ring1
      _ ≤ (distribution.expectation selectedValue +
            fraction * distribution.expectation value) -
          fraction * distribution.expectation value := shifted
      _ = distribution.expectation selectedValue := by
        ring1
  have complementNonnegative : 0 ≤ 1 - fraction :=
    RFAP.ConstructiveFraction.sub_nonneg_direct fractionAtMostOne
  have selectedLowerNonnegative :
      0 ≤ (1 - fraction) * distribution.expectation value :=
    RFAP.ConstructiveFraction.mul_nonneg_direct complementNonnegative
      meanNonnegative
  have squaredLower :
      ((1 - fraction) * distribution.expectation value) ^ 2 ≤
        distribution.expectation selectedValue ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct selectedLowerNonnegative
      selectedLower 2
  have productPointwise : (fun item =>
      value item * indicator event item) = selectedValue := rfl
  have cauchy := distribution.productExpectation_sq_le_poweredL2_mul
    value (indicator event)
  rw [productPointwise] at cauchy
  have indicatorSquare := distribution.expectation_congr
    (fun item => indicator event item ^ 2) (indicator event) (fun item => by
    cases selected : event item <;>
      simp only [indicator, selected] <;> ring1)
  have valueL2 : distribution.poweredL2 value =
      distribution.expectation (fun item => value item ^ 2) := rfl
  have indicatorL2 : distribution.poweredL2 (indicator event) =
      distribution.probability event := by
    calc
      distribution.poweredL2 (indicator event) =
          distribution.expectation (fun item => indicator event item ^ 2) :=
        rfl
      _ = distribution.expectation (indicator event) := by
        rw [indicatorSquare]
      _ = distribution.probability event :=
        distribution.expectation_indicator event
  rw [valueL2, indicatorL2] at cauchy
  calc
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 =
        ((1 - fraction) * distribution.expectation value) ^ 2 := by
      ring1
    _ ≤ distribution.expectation selectedValue ^ 2 := squaredLower
    _ ≤ distribution.expectation (fun item => value item ^ 2) *
        distribution.probability event := cauchy

/-- Executable strict event used by the standard Paley--Zygmund statement. -/
def aboveFractionOfMeanEvent {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) (fraction : Coordinate) : α → Bool :=
  fun item => decide
    (fraction * distribution.expectation value < value item)

/-- Standard divided Paley--Zygmund lower bound over a finite rational
distribution. -/
theorem paleyZygmund_bound {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (fraction : Coordinate)
    (fractionNonnegative : 0 ≤ fraction) (fractionAtMostOne : fraction ≤ 1)
    (valueNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (meanPositive : 0 < distribution.expectation value) :
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 /
        distribution.expectation (fun item => value item ^ 2) ≤
      distribution.probability
        (distribution.aboveFractionOfMeanEvent value fraction) := by
  have secondMomentPositive :
      0 < distribution.expectation (fun item => value item ^ 2) := by
    exact (RFAP.ConstructiveFraction.pow_pos_direct meanPositive 2).trans_le
      (distribution.expectation_sq_le_secondMoment value)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos secondMomentPositive).2
  have multiplicative := distribution.paleyZygmund_mul
    (distribution.aboveFractionOfMeanEvent value fraction) value fraction
    fractionNonnegative fractionAtMostOne valueNonnegative
    (by
      intro atom atomMember outside
      unfold aboveFractionOfMeanEvent at outside
      exact RFAP.ConstructiveFraction.le_of_not_gt_direct
        (decide_eq_false_iff_not.mp outside))
  calc
    (1 - fraction) ^ 2 * distribution.expectation value ^ 2 ≤
        distribution.expectation (fun item => value item ^ 2) *
          distribution.probability
            (distribution.aboveFractionOfMeanEvent value fraction) :=
      multiplicative
    _ = distribution.probability
          (distribution.aboveFractionOfMeanEvent value fraction) *
        distribution.expectation (fun item => value item ^ 2) := by
      ring1

end Distribution

end FiniteMeasure
