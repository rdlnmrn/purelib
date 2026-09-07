import CCL.Riemann.LegendrePositivityObstructions
import CCL.Riemann.LegendreSignedAcquisitionExamples

namespace CCL.Riemann.LegendrePositivityObstructionsExamples

open CCL.Riemann.LegendrePositivityAcquisition
open CCL.Riemann.LegendrePositivityObstructions

abbrev negativeInput := CCL.Riemann.LegendreSignedAcquisitionExamples.input (-1)

theorem negative_candidates (state : State negativeInput) : Nonpositive negativeInput state := by
  intro value possible
  change value = (⟨0, -1⟩ : Gaussian) at possible
  rw [possible]
  decide

theorem negative_all_budgets (state : State negativeInput) (fuel : Nat) :
    attempt negativeInput state fuel = .exhausted (advanceN state fuel) :=
  Nonpositive.attempt_exhausts state (negative_candidates state) fuel

/-- A certificate obtained by signed inspection itself obstructs all later
positive discovery on that retained branch. -/
theorem discovered_negative_all_budgets {tau : CoherentNamed} {state : State tau}
    {delta : Q} (positive : 0 < delta)
    (negative : CCL.Riemann.LegendreSignedAcquisition.Negative tau state delta) (fuel : Nat) :
    attempt tau state fuel = .exhausted (advanceN state fuel) :=
  Nonpositive.attempt_exhausts state (nonpositive_of_negative positive negative) fuel

end CCL.Riemann.LegendrePositivityObstructionsExamples
