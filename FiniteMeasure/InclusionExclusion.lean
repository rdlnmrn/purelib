import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Family
import FiniteMeasure.ContentOperations

/-!
# Executable finite inclusion--exclusion

The complete inclusion--exclusion expansion of a displayed event list is a
finite signed list.  It is generated recursively: retain every old
intersection term and add its intersection with the new head event with the
opposite sign.  This avoids a powerset or any ambient collection of events.
-/

namespace FiniteMeasure

/-- One executable event with its rational inclusion--exclusion
coefficient. -/
structure SignedEventTerm (α : Type) where
  event : α → Bool
  coefficient : Coordinate

namespace SignedEventTerm

/-- Intersect a signed term with one new event and reverse its sign. -/
def intersect {α : Type} (head : α → Bool)
    (term : SignedEventTerm α) : SignedEventTerm α where
  event := intersectionEvent head term.event
  coefficient := -term.coefficient

/-- Exact signed contribution of one term to a finite content. -/
def contribution {α : Type} (content : FiniteContent α)
    (term : SignedEventTerm α) : Coordinate :=
  term.coefficient * content.measure term.event

end SignedEventTerm

/-- All nonempty signed intersections of a displayed event family. -/
def inclusionExclusionTerms {α : Type} :
    List (α → Bool) → List (SignedEventTerm α)
  | [] => []
  | event :: remaining =>
      let tail := inclusionExclusionTerms remaining
      ⟨event, 1⟩ :: tail ++ tail.map (SignedEventTerm.intersect event)

private theorem inclusionExclusionTerms_length_add_one {α : Type} :
    ∀ events : List (α → Bool),
      (inclusionExclusionTerms events).length + 1 = 2 ^ events.length
  | [] => rfl
  | event :: remaining => by
      have inductionHypothesis :=
        inclusionExclusionTerms_length_add_one remaining
      simp only [inclusionExclusionTerms, List.length_cons,
        List.length_append, List.length_map, pow_succ]
      rw [← inductionHypothesis]
      ring1

/-- A family of length `n` produces exactly `2^n - 1` nonempty signed
intersection terms. -/
theorem inclusionExclusionTerms_length {α : Type}
    (events : List (α → Bool)) :
    (inclusionExclusionTerms events).length = 2 ^ events.length - 1 := by
  have count := inclusionExclusionTerms_length_add_one events
  rw [← count]
  exact (Nat.add_sub_cancel _ 1).symm

/-- Exact rational value of the displayed signed expansion. -/
def inclusionExclusionValue {α : Type} (content : FiniteContent α)
    (events : List (α → Bool)) : Coordinate :=
  ((inclusionExclusionTerms events).map
    (SignedEventTerm.contribution content)).sum

private theorem measure_intersectionEvent_comm {α : Type}
    (content : FiniteContent α) (left right : α → Bool) :
    content.measure (intersectionEvent left right) =
      content.measure (intersectionEvent right left) :=
  content.measure_congr _ _ (fun item => by
    unfold intersectionEvent
    cases left item <;> cases right item <;> rfl)

private theorem contribution_intersect {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (term : SignedEventTerm α) :
    SignedEventTerm.contribution content (term.intersect event) =
      -SignedEventTerm.contribution (content.restrict event) term := by
  unfold SignedEventTerm.contribution SignedEventTerm.intersect
  rw [content.restrict_measure]
  rw [measure_intersectionEvent_comm content term.event event]
  ring1

private theorem sum_contribution_intersect {α : Type}
    (content : FiniteContent α) (event : α → Bool) :
    ∀ terms : List (SignedEventTerm α),
      ((terms.map (SignedEventTerm.intersect event)).map
          (SignedEventTerm.contribution content)).sum =
        -((terms.map
          (SignedEventTerm.contribution (content.restrict event))).sum)
  | [] => by
      simp only [List.map_nil, List.sum_nil, neg_zero]
  | term :: remaining => by
      simp only [List.map_cons, List.sum_cons,
        contribution_intersect content event term,
        sum_contribution_intersect content event remaining]
      ring1

namespace FiniteContent

/-- Full inclusion--exclusion for every explicitly displayed finite event
family. -/
theorem inclusionExclusionValue_eq_measure_unionEvents {α : Type}
    (content : FiniteContent α) : ∀ events : List (α → Bool),
    inclusionExclusionValue content events =
      content.measure (unionEvents events)
  | [] => by
      unfold inclusionExclusionValue inclusionExclusionTerms
      simp only [List.map_nil, List.sum_nil]
      change 0 = content.measure (fun _ => false)
      exact content.measure_empty.symm
  | event :: remaining => by
      let tail := inclusionExclusionTerms remaining
      have tailFormula :=
        content.inclusionExclusionValue_eq_measure_unionEvents remaining
      have restrictedFormula :=
        FiniteContent.inclusionExclusionValue_eq_measure_unionEvents
          (content.restrict event) remaining
      have valuation := content.valuation event (unionEvents remaining)
      have overlapSame :
          content.measure
              (intersectionEvent (unionEvents remaining) event) =
            content.measure
              (intersectionEvent event (unionEvents remaining)) := by
        exact measure_intersectionEvent_comm content
          (unionEvents remaining) event
      unfold inclusionExclusionValue at tailFormula restrictedFormula
      unfold inclusionExclusionValue inclusionExclusionTerms
      simp only [List.map_cons, List.map_append, List.sum_cons,
        List.sum_append, SignedEventTerm.contribution]
      rw [sum_contribution_intersect content event tail,
        tailFormula, restrictedFormula, content.restrict_measure,
        overlapSame]
      calc
        1 * content.measure event +
              content.measure (unionEvents remaining) +
              -content.measure
                (intersectionEvent event (unionEvents remaining)) =
            (content.measure event +
                content.measure (unionEvents remaining)) -
              content.measure
                (intersectionEvent event (unionEvents remaining)) := by ring1
        _ = (content.measure (unionEvent event (unionEvents remaining)) +
              content.measure
                (intersectionEvent event (unionEvents remaining))) -
              content.measure
                (intersectionEvent event (unionEvents remaining)) := by
            rw [valuation]
        _ = content.measure
              (unionEvent event (unionEvents remaining)) := by ring1

end FiniteContent

namespace Distribution

/-- Probability form of full finite inclusion--exclusion. -/
theorem inclusionExclusionValue_eq_probability_unionEvents {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    inclusionExclusionValue distribution.toFiniteContent events =
      distribution.probability (unionEvents events) :=
  distribution.toFiniteContent
    |>.inclusionExclusionValue_eq_measure_unionEvents events

end Distribution

end FiniteMeasure
