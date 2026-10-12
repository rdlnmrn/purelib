module
public import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Lebesgue.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Uniqueness of finite Lebesgue decomposition

Any two displayed decompositions of one finite content into a part absolutely
continuous with respect to a source and a source-singular remainder agree on
every executable event.  The proof intersects the two explicit singularity
separators and uses only finite additivity and nonnegative event weights.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content

open Purelib.Data.Rat in
/-- An event contained on the retained atoms in a zero-mass event also has zero mass. -/
theorem measure_eq_zero_of_eventImplies {α : Type}
    (content : Content α) {event larger : α → Bool}
    (implication : EventImpliesOn content.atoms event larger)
    (zero : content.measure larger = 0) :
    content.measure event = 0 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · calc
      content.measure event ≤ content.measure larger :=
        eventWeight_mono implication
      _ = 0 := zero
  · exact content.measure_nonneg event

/-- Intersecting any event with a zero-mass right event gives zero mass. -/
theorem measure_intersection_eq_zero_of_right {α : Type}
    (content : Content α) (event zeroEvent : α → Bool)
    (zero : content.measure zeroEvent = 0) :
    content.measure (intersectionEvent event zeroEvent) = 0 := by
  apply content.measure_eq_zero_of_eventImplies
    (larger := zeroEvent) _ zero
  intro atom member selected
  cases eventSelected : event atom.item
  · simp only [intersectionEvent, eventSelected, Bool.false_and] at selected
    exact Bool.noConfusion selected
  · simpa only [intersectionEvent, eventSelected, Bool.true_and] using selected

/-- If a separator's complement is null, intersecting an event with that separator preserves its measurement. -/
theorem measure_eq_intersection_of_complement_eq_zero {α : Type}
    (content : Content α) (event separator : α → Bool)
    (outsideZero : content.measure (complementEvent separator) = 0) :
    content.measure event =
      content.measure (intersectionEvent event separator) := by
  have split := content.measure_intersection_add_complement event separator
  have outsideIntersectionZero :=
    content.measure_intersection_eq_zero_of_right event
      (complementEvent separator) outsideZero
  rw [outsideIntersectionZero, add_zero] at split
  exact split.symm

end Content

end Purelib.Measure

end
