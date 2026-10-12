module
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

/-- Require the intersection probability to equal the product of the two original event probabilities. -/
def Distribution.IndependentEvents {α : Type}
    (distribution : Distribution α) (left right : α → Bool) : Prop :=
  distribution.probability (intersectionEvent left right) =
    distribution.probability left * distribution.probability right

/-- Reversing the two events preserves their independence under the retained law. -/
theorem Distribution.independentEvents_symm {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents right left := by
  unfold IndependentEvents at independent ⊢
  calc
    distribution.probability (intersectionEvent right left) =
        distribution.probability (intersectionEvent left right) :=
      distribution.probability_congr _ _ (fun item => by
        unfold intersectionEvent
        cases left item <;> cases right item <;> rfl)
    _ = distribution.probability left * distribution.probability right :=
      independent
    _ = distribution.probability right * distribution.probability left := by
      ring1

/-- Complementing the right event preserves independence. -/
theorem Distribution.independentEvents_complement_right {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents left (complementEvent right) := by
  unfold IndependentEvents at independent ⊢
  have split := distribution.probability_intersection_add_complement
    left right
  have complement := distribution.probability_add_complement right
  have complementSub :
      distribution.probability (complementEvent right) =
        1 - distribution.probability right := by
    calc
      distribution.probability (complementEvent right) =
          distribution.probability right +
              distribution.probability (complementEvent right) -
            distribution.probability right := by
        ring1
      _ = 1 - distribution.probability right := by
        rw [complement]
  calc
    distribution.probability
          (intersectionEvent left (complementEvent right)) =
        distribution.probability
            (intersectionEvent left (complementEvent right)) +
          distribution.probability (intersectionEvent left right) -
            distribution.probability (intersectionEvent left right) := by
      ring1
    _ = distribution.probability left -
          distribution.probability (intersectionEvent left right) := by
      rw [add_comm, split]
    _ = distribution.probability left -
          distribution.probability left *
            distribution.probability right := by
      rw [independent]
    _ = distribution.probability left *
          distribution.probability (complementEvent right) := by
      rw [complementSub]
      ring1

/-- Complementing the left event preserves independence. -/
theorem Distribution.independentEvents_complement_left {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents (complementEvent left) right :=
  distribution.independentEvents_symm
    (distribution.independentEvents_complement_right
      (distribution.independentEvents_symm independent))

/-- Complementing both events preserves independence. -/
theorem Distribution.independentEvents_complements {α : Type}
    (distribution : Distribution α) {left right : α → Bool}
    (independent : distribution.IndependentEvents left right) :
    distribution.IndependentEvents
      (complementEvent left) (complementEvent right) :=
  distribution.independentEvents_complement_right
    (distribution.independentEvents_complement_left independent)

end Purelib.Measure

end

section
@[expose] public section

/-!
# Second moments of finite event counts

Expanding the square of a displayed occurrence count gives the exact sum of
the individual probabilities and twice the pair-intersection sum.  Applying
the finite Paley--Zygmund inequality at fraction zero then gives the standard
second-moment lower bound for a finite union.  All sums and events are
displayed and finite.
-/

namespace Purelib.Measure
namespace Distribution

/-- Recursively require independence between each event occurrence and every event in its retained tail. -/
def PairwiseIndependentEventList {α : Type}
    (distribution : Distribution α) : List (α → Bool) → Prop
  | [] => True
  | event :: remaining =>
      (∀ candidate, candidate ∈ remaining →
        distribution.IndependentEvents event candidate) ∧
      distribution.PairwiseIndependentEventList remaining
end Distribution

end Purelib.Measure

end
