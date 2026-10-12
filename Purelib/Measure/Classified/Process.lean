module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.Bound.Schedule
import Purelib.Approximation.OneSided.BoundProcess

public import Purelib.Measure.Refinement
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Distribution
import Purelib.Data.List.Prefix.Cursor
import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Effective finite event measurement

An event process is an executable controller over finite classified
frontiers.  It is measurable in the operational sense that every positive
rational request returns a finite refinement whose unresolved mass is below
that request.
-/

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain an executable request process whose exact classified frontiers refine and resolve every positive tolerance.

Each state has an original frontier; requests retain its certified refinement, accuracy and relation to the same initial
frontier. -/
structure EventProcess (α : Type) where
  /-- The retained process's exact state type. -/ State : Type
  /-- The original ordered classified frontier read from each state. -/ frontier : State → List (Classified α)
  /-- The retained initial process state. -/ initial : State
  /-- The executable next state for an original state and certified positive rational tolerance. -/ request : (state :
    State) → (epsilon : Fraction.Rational) → 0 < epsilon → State
  /-- Each request's exact resulting frontier refines the original frontier. -/ request_refines : ∀ state epsilon
    positive,
    FrontierRefines (frontier (request state epsilon positive))
      (frontier state)
  /-- Each request's exact frontier has unresolved weight below its supplied tolerance. -/ accurate : ∀ state epsilon
    positive,
    Resolves (frontier (request state epsilon positive)) epsilon
  /-- Every retained state frontier refines the same original initial frontier. -/ refinesInitial : ∀ state,
    FrontierRefines (frontier state) (frontier initial)

constructive_injectivity EventProcess

namespace EventProcess

open Purelib in
/-- Read the exact frontier event-bound intervals as a bound process, preserving the original states, requests and
initial state. -/
def toBoundProcess {α : Type} (process : EventProcess α) : Approximation.BoundProcess where
  State := process.State
  bound state := eventBound (process.frontier state)
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).eventBound_refines
  accurate state epsilon positive :=
    eventBound_width_lt (process.accurate state epsilon positive)
  refinesInitial state :=
    (process.refinesInitial state).eventBound_refines

section
open Purelib.Data.Rat
/-- An accuracy request cannot decrease the original frontier's lower classified weight. -/
theorem request_lower_mono {α : Type} (process : EventProcess α)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    lowerWeight (process.frontier state) ≤
      lowerWeight (process.frontier (process.request state epsilon positive)) :=
  (process.toBoundProcess.lowerRequestProcess epsilon positive).monotone state

/-- An accuracy request cannot increase the original frontier's upper classified weight. -/
theorem request_upper_antitone {α : Type} (process : EventProcess α)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    upperWeight (process.frontier (process.request state epsilon positive)) ≤
      upperWeight (process.frontier state) :=
  (process.toBoundProcess.upperRequestProcess epsilon positive).antitone state

/-- The frontier returned for a positive tolerance has event-bound width strictly below that tolerance. -/
theorem request_width_lt {α : Type} (process : EventProcess α)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (eventBound
      (process.frontier (process.request state epsilon positive))).width <
        epsilon :=
  eventBound_width_lt (process.accurate state epsilon positive)

end

section
open Purelib
/-- Run the supplied finite accuracy-request list through the exact retained process, starting at the supplied original
state. -/
def runRequests {α : Type} (process : EventProcess α)
    (state : process.State) (requests : List Approximation.AccuracyRequest) : process.State :=
  process.toBoundProcess.runRequests state requests

/-- After the exact request list, unresolved weight is below every tolerance occurring in that list. -/
theorem runRequests_unresolved_lt_of_mem {α : Type}
    (process : EventProcess α) (state : process.State)
    (requests : List Approximation.AccuracyRequest) (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) :
    unresolvedWeight (process.frontier
      (process.runRequests state requests)) < request.tolerance := by
  have accurate := process.toBoundProcess.runRequests_width_lt_of_mem
    state requests request member
  change (eventBound (process.frontier
    (process.runRequests state requests))).width < request.tolerance at accurate
  rw [eventBound_width] at accurate
  exact accurate

end

open Purelib in
open Purelib.Data.Rat in
/-- The exact scheduled result's event-bound interval refines that of its original starting state. -/
theorem runRequests_eventBound_refines {α : Type}
    (process : EventProcess α) (state : process.State)
    (requests : List Approximation.AccuracyRequest) :
    Interval.Refines
      (eventBound (process.frontier (process.runRequests state requests)))
      (eventBound (process.frontier state)) :=
  process.toBoundProcess.runRequests_refines state requests

end EventProcess

namespace Distribution

open Purelib in
/-- Construct a constant process from an exact finite distribution and decidable event.

Its sole state retains the original event-classified frontier, whose unresolved weight is zero for every positive
tolerance. -/
def exactEventProcess {α : Type} (distribution : Measure.Distribution α)
    (event : α → Bool) : EventProcess α where
  State := Unit
  frontier _ := distribution.eventFrontier event
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive :=
    FrontierRefines.refl _
  accurate state epsilon positive := by
    unfold Resolves
    rw [distribution.eventFrontier_unresolved_zero]
    exact positive
  refinesInitial state := FrontierRefines.refl _

end Distribution

end Purelib.Measure
