module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Operations
public import Purelib.Measure.Event.Family
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Executable finite inclusion--exclusion

The complete inclusion--exclusion expansion of a displayed event list is a
finite signed list.  It is generated recursively: retain every old
intersection term and add its intersection with the new head event with the
opposite sign.  This avoids a powerset or any ambient collection of events.
-/

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a Boolean event with its signed rational coefficient in a finite event expansion. -/
structure SignedEventTerm (α : Type) where
  /-- The exact Boolean event represented by this signed term. -/ event : α → Bool
  /-- The rational coefficient multiplying this event's measurement. -/ coefficient : Fraction.Rational

constructive_injectivity SignedEventTerm

namespace SignedEventTerm

/-- Intersect a signed term with the supplied event and negate its retained coefficient. -/
def intersect {α : Type} (head : α → Bool)
    (term : SignedEventTerm α) : SignedEventTerm α where
  event := intersectionEvent head term.event
  coefficient := -term.coefficient

open Purelib.Data.Rat in
/-- Multiply the retained signed coefficient by the content measurement of its exact event. -/
def contribution {α : Type} (content : Content α)
    (term : SignedEventTerm α) : Fraction.Rational :=
  term.coefficient * content.measure term.event

end SignedEventTerm

/-- Construct the signed nonempty intersections of the event list in its recursive finite order.

Retain the tail expansion once, then prepend the head event and append its intersections with the same tail terms using
opposite coefficients. Repeated input events retain their separate positions. -/
def inclusionExclusionTerms {α : Type} :
    List (α → Bool) → List (SignedEventTerm α)
  | [] => []
  | event :: remaining =>
      let tail := inclusionExclusionTerms remaining
      ⟨event, 1⟩ :: tail ++ tail.map (SignedEventTerm.intersect event)

/-- The recursive signed expansion has one fewer term than two raised to the input event count. -/
private theorem inclusionExclusionTerms_length_add_one {α : Type} :
    ∀ events : List (α → Bool),
      (inclusionExclusionTerms events).length + 1 = 2 ^ events.length
  | [] => rfl
  | event :: remaining => by
      have inductionHypothesis :=
        inclusionExclusionTerms_length_add_one remaining
      simp only [-eq_self, -iff_self, inclusionExclusionTerms, List.length_cons,
        Data.List.Append.length_append, Data.List.Map.length_map, pow_succ]
      rw [← inductionHypothesis]
      ring1

/-- The signed nonempty-intersection expansion has exactly two to the event count minus one terms. -/
theorem inclusionExclusionTerms_length {α : Type}
    (events : List (α → Bool)) :
    (inclusionExclusionTerms events).length = 2 ^ events.length - 1 := by
  have count := inclusionExclusionTerms_length_add_one events
  rw [← count]
  exact (Data.Nat.Subtraction.add_sub_cancel_right _ 1).symm

open Purelib.Data.Rat in
/-- Sum the exact signed contributions of the recursively constructed event expansion. -/
def inclusionExclusionValue {α : Type} (content : Content α)
    (events : List (α → Bool)) : Fraction.Rational :=
  ((inclusionExclusionTerms events).map
    (SignedEventTerm.contribution content)).sum

/-- Exchanging the two Boolean intersection operands preserves their content measurement. -/
private theorem measure_intersectionEvent_comm {α : Type}
    (content : Content α) (left right : α → Bool) :
    content.measure (intersectionEvent left right) =
      content.measure (intersectionEvent right left) :=
  content.measure_congr _ _ (fun item => by
    unfold intersectionEvent
    cases left item <;> cases right item <;> rfl)

/-- Intersecting a signed term with an event gives its negated contribution in the content restricted to that event. -/
private theorem contribution_intersect {α : Type}
    (content : Content α) (event : α → Bool)
    (term : SignedEventTerm α) :
    SignedEventTerm.contribution content (term.intersect event) =
      -SignedEventTerm.contribution (content.restrict event) term := by
  unfold SignedEventTerm.contribution SignedEventTerm.intersect
  rw [content.restrict_measure]
  rw [measure_intersectionEvent_comm content term.event event]
  ring1

/-- The sum of intersected signed terms is the negative of their sum in the corresponding restricted content. -/
private theorem sum_contribution_intersect {α : Type}
    (content : Content α) (event : α → Bool) :
    ∀ terms : List (SignedEventTerm α),
      ((terms.map (SignedEventTerm.intersect event)).map
          (SignedEventTerm.contribution content)).sum =
        -((terms.map
          (SignedEventTerm.contribution (content.restrict event))).sum)
  | [] => by
      simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil, neg_zero]
      rfl
  | term :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, List.sum_cons,
        contribution_intersect content event term,
        sum_contribution_intersect content event remaining]
      ring1

namespace Content

/-- The finite signed intersection expansion equals the content measurement of the original event union.

The recursive proof retains the exact tail expansion and applies the two-event valuation identity at each head event. -/
theorem inclusionExclusionValue_eq_measure_unionEvents {α : Type}
    (content : Content α) : ∀ events : List (α → Bool),
    inclusionExclusionValue content events =
      content.measure (unionEvents events)
  | [] => by
      unfold inclusionExclusionValue inclusionExclusionTerms
      simp only [-eq_self, -iff_self, List.map_nil, List.sum_nil]
      change 0 = content.measure (fun _ => false)
      exact content.measure_empty.symm
  | event :: remaining => by
      let tail := inclusionExclusionTerms remaining
      have tailFormula :=
        content.inclusionExclusionValue_eq_measure_unionEvents remaining
      have restrictedFormula :=
        Content.inclusionExclusionValue_eq_measure_unionEvents
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
      simp only [-eq_self, -iff_self, List.map_cons, Data.List.Map.map_append, List.sum_cons,
        Data.List.Fold.sum_append (fun value : Purelib.Data.Rat.Fraction.Rational => by ring1) (fun a b c :
          Purelib.Data.Rat.Fraction.Rational => by ring1), SignedEventTerm.contribution]
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

end Content

namespace Distribution

/-- The signed intersection expansion of a finite distribution equals its probability of the original event union. -/
theorem inclusionExclusionValue_eq_probability_unionEvents {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    inclusionExclusionValue distribution.toContent events =
      distribution.probability (unionEvents events) :=
  distribution.toContent
    |>.inclusionExclusionValue_eq_measure_unionEvents events

end Distribution

end Purelib.Measure
