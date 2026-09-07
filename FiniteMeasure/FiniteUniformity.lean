import mathlib.Data.ConstructiveList
import FiniteMeasure.ConvergenceModes
import FiniteMeasure.Family

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

namespace FiniteMeasure

private theorem event_eq_false_of_unionEvents_eq_false_of_mem
    {α : Type} :
    ∀ (events : List (α → Bool)) (event : α → Bool),
      event ∈ events → ∀ item,
        unionEvents events item = false → event item = false
  | [], event, member, item, outside => by
      cases member
  | head :: remaining, event, member, item, outside => by
      have separated : head item = false ∧
          unionEvents remaining item = false := by
        cases headSelected : head item <;>
          cases tailSelected : unionEvents remaining item <;>
          simp_all [unionEvents, unionEvent]
      rcases List.mem_cons.mp member with same | tail
      · subst event
        exact separated.1
      · exact event_eq_false_of_unionEvents_eq_false_of_mem
          remaining event tail item separated.2

namespace Distribution

/-- Threshold-error events for every member of one displayed observable
family. -/
def simultaneousSeparationEvents {α : Type}
    (threshold : Coordinate) (approximations : List (α → Coordinate))
    (target : α → Coordinate) : List (α → Bool) :=
  approximations.map fun approximation =>
    separationAtLeast threshold approximation target

/-- The single exceptional event on which at least one displayed
approximation misses the common threshold. -/
def simultaneousExceptionalEvent {α : Type}
    (threshold : Coordinate) (approximations : List (α → Coordinate))
    (target : α → Coordinate) : α → Bool :=
  unionEvents (simultaneousSeparationEvents threshold approximations target)

/-- Sum of the individual error probabilities.  This is an executable
rational upper budget for the simultaneous exceptional event. -/
def simultaneousFailureBudget {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (approximations : List (α → Coordinate))
    (target : α → Coordinate) : Coordinate :=
  ((simultaneousSeparationEvents threshold approximations target).map
    distribution.probability).sum

/-- Finite subadditivity bounds the simultaneous exceptional event. -/
theorem probability_simultaneousExceptionalEvent_le_failureBudget
    {α : Type} (distribution : Distribution α)
    (threshold : Coordinate) (approximations : List (α → Coordinate))
    (target : α → Coordinate) :
    distribution.probability
        (simultaneousExceptionalEvent threshold approximations target) ≤
      distribution.simultaneousFailureBudget threshold approximations
        target :=
  distribution.probability_unionEvents_le_sum
    (simultaneousSeparationEvents threshold approximations target)

/-- Outside the one simultaneous exceptional event, every displayed
approximation is strictly within the common rational threshold on every
displayed atom. -/
theorem separation_lt_of_mem_of_outside_simultaneousExceptionalEvent
    {α : Type} (distribution : Distribution α)
    (threshold : Coordinate) (approximations : List (α → Coordinate))
    (target approximation : α → Coordinate)
    (member : approximation ∈ approximations)
    (atom : Weighted α) (_atomMember : atom ∈ distribution.atoms)
    (outside : simultaneousExceptionalEvent threshold approximations target
      atom.item = false) :
    rationalSeparation (approximation atom.item) (target atom.item) <
      threshold := by
  have eventMember : separationAtLeast threshold approximation target ∈
      simultaneousSeparationEvents threshold approximations target := by
    exact QuotientFreeList.mem_map.mpr ⟨approximation, member, rfl⟩
  have eventFalse : separationAtLeast threshold approximation target
      atom.item = false :=
    event_eq_false_of_unionEvents_eq_false_of_mem
      (simultaneousSeparationEvents threshold approximations target)
      (separationAtLeast threshold approximation target) eventMember
      atom.item outside
  have notThreshold : ¬threshold ≤
      rationalSeparation (approximation atom.item) (target atom.item) := by
    unfold separationAtLeast at eventFalse
    exact decide_eq_false_iff_not.mp eventFalse
  exact RFAP.ConstructiveFraction.lt_of_not_ge_direct notThreshold

/-- Packaged finite uniformization certificate. -/
structure UniformOutsideBudget {α : Type}
    (distribution : Distribution α)
    (approximations : List (α → Coordinate))
    (target : α → Coordinate) where
  threshold : Coordinate
  threshold_positive : 0 < threshold
  exceptional : α → Bool
  failure : Coordinate
  failure_nonnegative : 0 ≤ failure
  probability_le : distribution.probability exceptional ≤ failure
  outside : ∀ approximation, approximation ∈ approximations →
    ∀ atom, atom ∈ distribution.atoms → exceptional atom.item = false →
      rationalSeparation (approximation atom.item) (target atom.item) <
        threshold

/-- Construct the simultaneous certificate directly from a common threshold
and a displayed finite approximation family. -/
def uniformOutsideBudget {α : Type} (distribution : Distribution α)
    (approximations : List (α → Coordinate))
    (target : α → Coordinate) (threshold : Coordinate)
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

/-- A sufficiently small displayed failure sum gives one small exceptional
event outside which the entire finite family is uniformly accurate. -/
theorem accurate {α : Type} {distribution : Distribution α}
    {approximations : List (α → Coordinate)}
    {target : α → Coordinate}
    (budget : UniformOutsideBudget distribution approximations target)
    (epsilon : Coordinate) (small : budget.failure < epsilon) :
    distribution.probability budget.exceptional < epsilon :=
  budget.probability_le.trans_lt small

end UniformOutsideBudget

end Distribution

end FiniteMeasure
