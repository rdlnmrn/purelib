module
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Independence.Basic
public import Purelib.Measure.Distribution.Kernel.Basic

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

/-- Events depending on separate product coordinates are independent under the exact product distribution.

The original finite product retains both marginal distributions; its coordinate-event rectangle probability is the
product of the original marginal probabilities. -/
theorem Distribution.product_independentEvents_coordinates
    {α β : Type} (left : Distribution α) (right : Distribution β)
    (leftEvent : α → Bool) (rightEvent : β → Bool) :
    (left.product right).IndependentEvents
      (fun pair => leftEvent pair.1)
      (fun pair => rightEvent pair.2) := by
  unfold IndependentEvents
  change (left.product right).probability
      (fun pair => leftEvent pair.1 && rightEvent pair.2) =
    (left.product right).probability (fun pair => leftEvent pair.1) *
      (left.product right).probability (fun pair => rightEvent pair.2)
  have leftMarginal :
      (left.product right).probability (fun pair => leftEvent pair.1) =
        left.probability leftEvent := by
    calc
      (left.product right).probability (fun pair => leftEvent pair.1) =
          (left.product right).probability
            (fun pair => leftEvent pair.1 && true) :=
        (left.product right).probability_congr _ _ (fun pair => by
          simp only [Bool.and_true, -eq_self, -iff_self]
          rfl)
      _ = left.probability leftEvent * right.probability (fun _ => true) :=
        left.product_probability_rectangle right leftEvent (fun _ => true)
      _ = left.probability leftEvent := by
        rw [right.probability_true, mul_one]
  have rightMarginal :
      (left.product right).probability (fun pair => rightEvent pair.2) =
        right.probability rightEvent := by
    calc
      (left.product right).probability (fun pair => rightEvent pair.2) =
          (left.product right).probability
            (fun pair => true && rightEvent pair.2) :=
        (left.product right).probability_congr _ _ (fun pair => by
          simp only [Bool.true_and, -eq_self, -iff_self]
          rfl)
      _ = left.probability (fun _ => true) * right.probability rightEvent :=
        left.product_probability_rectangle right (fun _ => true) rightEvent
      _ = right.probability rightEvent := by
        rw [left.probability_true, one_mul]
  rw [left.product_probability_rectangle right leftEvent rightEvent,
    leftMarginal, rightMarginal]
end Purelib.Measure

end
