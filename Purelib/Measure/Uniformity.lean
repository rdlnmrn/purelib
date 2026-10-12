module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.EventFamily
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Measure.Event.RationalDistance
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Measure.Event.Family
import Purelib.Measure.Distribution.Convergence.InMeasure
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Simultaneous finite accuracy outside one exceptional event

For a displayed finite family of rational observables, union their explicit
threshold-error events.  Outside that one union every member is uniformly
accurate at the same threshold, while finite subadditivity bounds the union's
probability by the sum of the individual failure probabilities.

This is the executable finite core of the exceptional-set step in Egorov's
theorem.  It does not assert convergence of a sequence or quantify over an
infinite family.
-/

namespace Purelib.Measure

/-- An event in a finite list is false wherever the list's union event is false. -/
private theorem event_eq_false_of_unionEvents_eq_false_of_mem
    {α : Type} :
    ∀ (events : List (α → Bool)) (event : α → Bool),
      event ∈ events → ∀ item,
        unionEvents events item = false → event item = false
  | [], event, member, item, outside => by
      cases member
  | head :: remaining, event, member, item, outside =>
      event_eq_false_of_mem_of_unionEvents_eq_false (head :: remaining) event member item outside

namespace Distribution

section
open Purelib.Data.Rat
/-- List the threshold-separation event for every retained approximation occurrence. -/
def simultaneousSeparationEvents {α : Type}
    (threshold : Fraction.Rational) (approximations : List (α → Fraction.Rational))
    (target : α → Fraction.Rational) : List (α → Bool) :=
  approximations.map fun approximation =>
    separationAtLeast threshold approximation target

/-- Take the union of the retained approximations' threshold-separation events. -/
def simultaneousExceptionalEvent {α : Type}
    (threshold : Fraction.Rational) (approximations : List (α → Fraction.Rational))
    (target : α → Fraction.Rational) : α → Bool :=
  unionEvents (simultaneousSeparationEvents threshold approximations target)

/-- Sum probabilities of the retained threshold-separation events, counting repeated approximation occurrences. -/
def simultaneousFailureBudget {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (approximations : List (α → Fraction.Rational))
    (target : α → Fraction.Rational) : Fraction.Rational :=
  ((simultaneousSeparationEvents threshold approximations target).map
    distribution.probability).sum

/-- The simultaneous exceptional event has probability at most the original sum of failure probabilities. -/
theorem probability_simultaneousExceptionalEvent_le_failureBudget
    {α : Type} (distribution : Distribution α)
    (threshold : Fraction.Rational) (approximations : List (α → Fraction.Rational))
    (target : α → Fraction.Rational) :
    distribution.probability
        (simultaneousExceptionalEvent threshold approximations target) ≤
      distribution.simultaneousFailureBudget threshold approximations
        target :=
  distribution.probability_unionEvents_le_sum
    (simultaneousSeparationEvents threshold approximations target)

end

open Purelib.Data.List in
open Purelib.Data.Rat in
/-- Outside the union event, each retained approximation is strictly within the threshold of the target. -/
theorem separation_lt_of_mem_of_outside_simultaneousExceptionalEvent
    {α : Type} (distribution : Distribution α)
    (threshold : Fraction.Rational) (approximations : List (α → Fraction.Rational))
    (target approximation : α → Fraction.Rational)
    (member : approximation ∈ approximations)
    (atom : Weighted α) (_atomMember : atom ∈ distribution.atoms)
    (outside : simultaneousExceptionalEvent threshold approximations target
      atom.item = false) :
    Distance.rationalSeparation (approximation atom.item) (target atom.item) <
      threshold := by
  have eventMember : separationAtLeast threshold approximation target ∈
      simultaneousSeparationEvents threshold approximations target := by
    exact Map.mem_map.mpr ⟨approximation, member, rfl⟩
  have eventFalse : separationAtLeast threshold approximation target
      atom.item = false :=
    event_eq_false_of_unionEvents_eq_false_of_mem
      (simultaneousSeparationEvents threshold approximations target)
      (separationAtLeast threshold approximation target) eventMember
      atom.item outside
  have notThreshold : ¬threshold ≤
      Distance.rationalSeparation (approximation atom.item) (target atom.item) := by
    unfold separationAtLeast at eventFalse
    intro comparison
    have selected : decide (threshold ≤
        Distance.rationalSeparation (approximation atom.item) (target atom.item)) = true :=
      decide_eq_true comparison
    rw [selected] at eventFalse
    exact Bool.noConfusion eventFalse
  exact Fraction.Order.Arithmetic.lt_of_not_ge_direct notThreshold

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- A common approximation threshold and exceptional-event probability budget.

The certificate retains the original finite law, approximation list and target, and proves strict pointwise accuracy on
their atoms outside the supplied event. -/
structure UniformOutsideBudget {α : Type}
    (distribution : Distribution α)
    (approximations : List (α → Fraction.Rational))
    (target : α → Fraction.Rational) where
  /-- The common rational accuracy threshold for all retained approximations. -/ threshold : Fraction.Rational
  /-- The retained accuracy threshold is strictly positive. -/ threshold_positive : 0 < threshold
  /-- The retained Boolean exceptional event on the original carrier. -/ exceptional : α → Bool
  /-- The retained upper bound on exceptional-event probability. -/ failure : Fraction.Rational
  /-- The probability budget is nonnegative. -/ failure_nonnegative : 0 ≤ failure
  /-- The original law assigns the exceptional event probability at most the retained budget. -/ probability_le :
    distribution.probability exceptional ≤ failure
  /-- Every retained approximation is strictly within the threshold of the target on original atoms outside the event.
  -/ outside : ∀ approximation, approximation ∈ approximations →
    ∀ atom, atom ∈ distribution.atoms → exceptional atom.item = false →
      Distance.rationalSeparation (approximation atom.item) (target atom.item) <
        threshold

constructive_injectivity UniformOutsideBudget

open Purelib.Data.Rat in
/-- Build a simultaneous accuracy certificate from the union of the exact separation events.

Its retained failure budget is the sum of the original event probabilities, so repeated approximation occurrences
contribute separately. -/
def uniformOutsideBudget {α : Type} (distribution : Distribution α)
    (approximations : List (α → Fraction.Rational))
    (target : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold) :
    UniformOutsideBudget distribution approximations target where
  threshold := threshold
  threshold_positive := positive
  exceptional := simultaneousExceptionalEvent threshold approximations target
  failure := distribution.simultaneousFailureBudget threshold approximations
    target
  failure_nonnegative := by
    have nonnegative : ∀ events : List (α → Bool),
        0 ≤ (events.map distribution.probability).sum := by
      intro events
      induction events with
      | nil => exact le_rfl
      | cons event remaining inductionHypothesis =>
          simp only [List.map_cons, List.sum_cons]
          exact add_nonneg (distribution.probability_nonneg event)
            inductionHypothesis
    exact nonnegative
      (simultaneousSeparationEvents threshold approximations target)
  probability_le :=
    distribution.probability_simultaneousExceptionalEvent_le_failureBudget
      threshold approximations target
  outside := by
    intro approximation member atom atomMember outside
    exact distribution
      |>.separation_lt_of_mem_of_outside_simultaneousExceptionalEvent
        threshold approximations target approximation member atom atomMember
        outside

namespace UniformOutsideBudget

open Purelib.Data.Rat in
/-- A failure budget below the requested epsilon makes the retained exceptional-event probability strictly smaller than
epsilon. -/
theorem accurate {α : Type} {distribution : Distribution α}
    {approximations : List (α → Fraction.Rational)}
    {target : α → Fraction.Rational}
    (budget : UniformOutsideBudget distribution approximations target)
    (epsilon : Fraction.Rational) (small : budget.failure < epsilon) :
    distribution.probability budget.exceptional < epsilon :=
  budget.probability_le.trans_lt small

end UniformOutsideBudget

end Distribution

end Purelib.Measure
