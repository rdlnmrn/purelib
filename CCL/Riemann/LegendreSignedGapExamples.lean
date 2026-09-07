import CCL.Riemann.LegendreSignedGap
import CCL.Riemann.LegendreSignedAcquisitionExamples

namespace CCL.Riemann.LegendreSignedGapExamples

open CCL.Riemann.LegendrePositivityAcquisition (initial State Gaussian Word)
open CCL.Riemann.LegendreSignedGap
open CCL.Riemann.LegendreSignedAcquisitionExamples (input delayed)

theorem positive_gap (state : State (input 1)) : Gap (input 1) state 1 := by
  intro value possible
  change value = (⟨0, 1⟩ : Gaussian) at possible
  subst value
  exact .inr (by decide)

theorem negative_gap (state : State (input (-1))) : Gap (input (-1)) state 1 := by
  intro value possible
  change value = (⟨0, -1⟩ : Gaussian) at possible
  subst value
  exact .inl (by decide)

theorem delayed_gap (state : State delayed) : Gap delayed state 1 := by
  intro value possible
  change value = CCL.Riemann.LegendrePositivityAcquisitionExamples.imaginaryUnit at possible
  subst value
  exact .inr (by decide)

theorem requested_positive :
    (requested (input 1) (initial (input 1)) 1 (by decide) (positive_gap _)).2.isPositive = true := by
  decide

theorem requested_negative :
    (requested (input (-1)) (initial (input (-1))) 1 (by decide) (negative_gap _)).2.isPositive =
      false := by decide

def delayedReport := canonical delayed (initial delayed) 1 (by decide) (delayed_gap _)

theorem canonical_delayed_positive : delayedReport.outcome.isPositive = true := by decide

theorem canonical_delayed_count : delayedReport.count = 4 := by decide

/-- The computed sufficient budget is for the original runner, not just a
new evaluator that assumes a passing state. -/
theorem original_runner_budget :
    ∃ certificate, CCL.Riemann.LegendrePositivityAcquisition.attempt delayed (initial delayed)
      (delayedReport.count + 1) = .ready certificate :=
  ⟨(delayedReport.finishPositive (by decide)).val,
    (delayedReport.finishPositive (by decide)).property⟩

theorem canonical_word_ready (word : Word) :
    ∃ result, delayedReport.outcome.transport word = .inl result := ⟨_, rfl⟩

theorem canonical_fold_ready (word : Word) :
    ∃ result, delayedReport.outcome.fold word = .inl result := ⟨_, rfl⟩

end CCL.Riemann.LegendreSignedGapExamples
