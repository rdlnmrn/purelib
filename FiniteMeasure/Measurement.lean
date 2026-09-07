import FiniteMeasure.Refinement
import FiniteMeasure.Schedule
import FiniteMeasure.Probability
import FiniteMeasure.OneSidedProcess

/-!
# Effective finite event measurement

An event process is an executable controller over finite classified
frontiers.  It is measurable in the operational sense that every positive
rational request returns a finite refinement whose unresolved mass is below
that request.
-/

namespace FiniteMeasure

/-- Arbitrary-accuracy finite measurement of one event. -/
structure EventProcess (α : Type) where
  State : Type
  frontier : State → List (Classified α)
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    FrontierRefines (frontier (request state epsilon positive))
      (frontier state)
  accurate : ∀ state epsilon positive,
    Resolves (frontier (request state epsilon positive)) epsilon
  refinesInitial : ∀ state, FrontierRefines (frontier state) (frontier initial)

namespace EventProcess

/-- Forget cell syntax only after retaining its rational lower/upper event
bound. -/
def toBoundProcess {α : Type} (process : EventProcess α) : BoundProcess where
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

/-- Lower certified event content can only rise after a request. -/
theorem request_lower_mono {α : Type} (process : EventProcess α)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    lowerWeight (process.frontier state) ≤
      lowerWeight (process.frontier (process.request state epsilon positive)) :=
  (process.toBoundProcess.lowerRequestProcess epsilon positive).monotone state

/-- Upper certified event content can only fall after a request. -/
theorem request_upper_antitone {α : Type} (process : EventProcess α)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    upperWeight (process.frontier (process.request state epsilon positive)) ≤
      upperWeight (process.frontier state) :=
  (process.toBoundProcess.upperRequestProcess epsilon positive).antitone state

/-- The returned lower and upper event contents differ by less than the
requested rational tolerance. -/
theorem request_width_lt {α : Type} (process : EventProcess α)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (eventBound
      (process.frontier (process.request state epsilon positive))).width <
        epsilon :=
  eventBound_width_lt (process.accurate state epsilon positive)

/-- Execute a displayed finite batch of event-measure accuracy requests. -/
def runRequests {α : Type} (process : EventProcess α)
    (state : process.State) (requests : List AccuracyRequest) : process.State :=
  process.toBoundProcess.runRequests state requests

/-- One final finite event frontier has unresolved mass below every tolerance
in the displayed request batch. -/
theorem runRequests_unresolved_lt_of_mem {α : Type}
    (process : EventProcess α) (state : process.State)
    (requests : List AccuracyRequest) (request : AccuracyRequest)
    (member : request ∈ requests) :
    unresolvedWeight (process.frontier
      (process.runRequests state requests)) < request.tolerance := by
  have accurate := process.toBoundProcess.runRequests_width_lt_of_mem
    state requests request member
  change (eventBound (process.frontier
    (process.runRequests state requests))).width < request.tolerance at accurate
  rw [eventBound_width] at accurate
  exact accurate

/-- The final event enclosure in a finite batch refines the enclosure at the
supplied starting state. -/
theorem runRequests_eventBound_refines {α : Type}
    (process : EventProcess α) (state : process.State)
    (requests : List AccuracyRequest) :
    Bound.Refines
      (eventBound (process.frontier (process.runRequests state requests)))
      (eventBound (process.frontier state)) :=
  process.toBoundProcess.runRequests_refines state requests

end EventProcess

namespace Distribution

/-- Every Boolean event on a displayed finite distribution is an exact
zero-uncertainty event process. -/
def exactEventProcess {α : Type} (distribution : Distribution α)
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

end FiniteMeasure
