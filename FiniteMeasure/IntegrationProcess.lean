import FiniteMeasure.Integration
import FiniteMeasure.Schedule
import FiniteMeasure.OneSidedProcess

/-!
# Effective finite integration

An integration process is an executable controller over finite rational
lower/upper sums.  Every positive rational request returns a certified finite
subdivision with smaller oscillation.  This is the operational content of
integrability used here; no limiting integral value is constructed.
-/

namespace FiniteMeasure

/-- Arbitrary-accuracy finite integration by certified subdivision. -/
structure IntegrationProcess (α : Type) where
  State : Type
  frontier : State → List (IntegrationCell α)
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    IntegrationFrontierRefines
      (frontier (request state epsilon positive)) (frontier state)
  accurate : ∀ state epsilon positive,
    integralOscillation (frontier (request state epsilon positive)) < epsilon
  refinesInitial : ∀ state,
    IntegrationFrontierRefines (frontier state) (frontier initial)

namespace IntegrationProcess

/-- Retain only the certified rational lower/upper integral enclosure. -/
def toBoundProcess {α : Type} (process : IntegrationProcess α) :
    BoundProcess where
  State := process.State
  bound state := integralBound (process.frontier state)
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).integralBound_refines
  accurate state epsilon positive := by
    rw [integralBound_width]
    exact process.accurate state epsilon positive
  refinesInitial state :=
    (process.refinesInitial state).integralBound_refines

theorem request_lower_mono {α : Type} (process : IntegrationProcess α)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    lowerIntegral (process.frontier state) ≤
      lowerIntegral (process.frontier
        (process.request state epsilon positive)) :=
  (process.toBoundProcess.lowerRequestProcess epsilon positive).monotone state

theorem request_upper_antitone {α : Type} (process : IntegrationProcess α)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    upperIntegral (process.frontier
      (process.request state epsilon positive)) ≤
        upperIntegral (process.frontier state) :=
  (process.toBoundProcess.upperRequestProcess epsilon positive).antitone state

theorem request_width_lt {α : Type} (process : IntegrationProcess α)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (integralBound (process.frontier
      (process.request state epsilon positive))).width < epsilon := by
  rw [integralBound_width]
  exact process.accurate state epsilon positive

/-- Execute a displayed finite batch of integration requests. -/
def runRequests {α : Type} (process : IntegrationProcess α)
    (state : process.State) (requests : List AccuracyRequest) : process.State :=
  process.toBoundProcess.runRequests state requests

/-- One final finite subdivision meets every tolerance in the displayed
request batch. -/
theorem runRequests_oscillation_lt_of_mem {α : Type}
    (process : IntegrationProcess α) (state : process.State)
    (requests : List AccuracyRequest) (request : AccuracyRequest)
    (member : request ∈ requests) :
    integralOscillation
      (process.frontier (process.runRequests state requests)) <
        request.tolerance := by
  have accurate := process.toBoundProcess.runRequests_width_lt_of_mem
    state requests request member
  change (integralBound (process.frontier
    (process.runRequests state requests))).width < request.tolerance at accurate
  rw [integralBound_width] at accurate
  exact accurate

/-- Exact displayed simple functions form a constant zero-uncertainty
integration process. -/
def exactSimple {α : Type}
    (entries : List (Weighted (α × Coordinate))) : IntegrationProcess α where
  State := Unit
  frontier _ := entries.map fun entry =>
    IntegrationCell.exact entry.item.1 entry.weight entry.item.2
      entry.nonnegative
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive := IntegrationFrontierRefines.refl _
  accurate state epsilon positive := by
    have exactWidth := integralBound_exact_width entries
    rw [integralBound_width] at exactWidth
    rw [exactWidth]
    exact positive
  refinesInitial state := IntegrationFrontierRefines.refl _

end IntegrationProcess

end FiniteMeasure
