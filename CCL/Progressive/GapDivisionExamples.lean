import CCL.Progressive.GapDivision
import CCL.Progressive.BoundedDivisionExamples
import CCL.Progressive.DivisionObstructionsExamples

namespace CCL.ProgressiveGapDivisionExamples

open CCL.ProgressivePartialDivision (State)
open CCL.ProgressiveGapDivision
open CCL.ProgressiveBoundedDivisionExamples (zeroInput oneInput tinyInput tinyValue tiny_nonzero delayed)

def tinyGap := RFAP.ConstructiveGaussian.Gaussian.normSq tinyValue

theorem tinyGap_positive : 0 < tinyGap :=
  RFAP.ConstructiveGaussian.Gaussian.normSq_pos tiny_nonzero

theorem zero_gap : Gap zeroInput (State.initial zeroInput) 1 :=
  fun possible => .inl possible

theorem one_gap : Gap oneInput (State.initial oneInput) 1 := by
  intro value possible
  change value = 1 at possible
  subst value
  exact .inr (by decide)

theorem tiny_gap : Gap tinyInput (State.initial tinyInput) tinyGap := by
  intro value possible
  change value = tinyValue at possible
  subst value
  exact .inr le_rfl

theorem delayed_gap : Gap delayed (State.initial delayed) 1 := by
  intro value possible
  change value = 1 at possible
  subst value
  exact .inr (by decide)

theorem zero_excluded :
    (acquire (State.initial zeroInput) 1 (by decide) zero_gap).2.isPrepared = false := by decide

theorem one_prepared :
    (acquire (State.initial oneInput) 1 (by decide) one_gap).2.isPrepared = true := by decide

/-- The input previously classified as small at threshold one now has a
preparation, using its independently supplied smaller nonzero gap. -/
theorem tiny_prepared :
    (acquire (State.initial tinyInput) tinyGap tinyGap_positive tiny_gap).2.isPrepared = true := by
  have prepared : ∃ evidence,
      (CCL.ProgressiveBoundedDivision.acquire (State.initial tinyInput)
        tinyGap tinyGap_positive).outcome = .inl evidence := by
    apply CCL.ProgressiveBoundedDivision.classify_apart
    change ¬ 2 * (0 + tinyGap) < tinyGap
    have lower : tinyGap ≤ 2 * (0 + tinyGap) := by
      calc
        tinyGap ≤ tinyGap + tinyGap := le_add_of_nonneg_left tinyGap_positive.le
        _ = 2 * (0 + tinyGap) := by ring1
    exact not_lt_of_ge lower
  obtain ⟨evidence, equal⟩ := prepared
  unfold acquire
  dsimp only
  rw [equal]
  rfl

theorem delayed_prepared :
    (acquire (State.initial delayed) 1 (by decide) delayed_gap).2.isPrepared = true := by decide

abbrev paddedZero := CCL.ProgressiveDivisionObstructionsExamples.paddedZero

theorem padded_gap (state : State paddedZero) : Gap paddedZero state 1 :=
  fun possible => .inl possible

/-- Exact exclusion also works when every finite ball has positive radius. -/
theorem padded_zero_excluded :
    (acquire (State.initial paddedZero) 1 (by decide) (padded_gap _)).2.isPrepared = false := by decide

end CCL.ProgressiveGapDivisionExamples
