module

public import Purelib.Data.List.Event
public import Purelib.Data.List.Multiplicity
public import Purelib.Measure.Weighted.Consolidation

section
public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Measure

open Purelib in
/-- Counting the singleton event in a sample list equals counting occurrences of its exact target payload. -/
theorem countEvent_atomEvent {α : Type} [DecidableEq α]
    (samples : List α) (target : α) :
    Data.List.countEvent samples (atomEvent target) = Data.List.countItem samples target := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      by_cases equal : item = target
      · simp only [-eq_self, -iff_self, Data.List.countEvent, atomEvent,
          Data.List.countItem, decide_eq_true equal, if_pos equal,
          if_pos rfl, inductionHypothesis]
        rfl
      · simp only [-eq_self, -iff_self, Data.List.countEvent, atomEvent,
          Data.List.countItem, decide_eq_false equal, if_neg equal,
          if_neg (by decide : ¬ false = true), inductionHypothesis]
        rfl
end Purelib.Measure

end
