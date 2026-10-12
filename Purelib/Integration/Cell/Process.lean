module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Weighted.Basic
import Purelib.Integration.Cell.Basic
import Purelib.Integration.Cell.Exact
public import Purelib.Integration.Cell.Refinement
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.Bound.Schedule
import Purelib.Approximation.OneSided.BoundProcess
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Basic

@[expose] public section

/-!
# Effective finite integration

An integration process is an executable controller over finite rational
lower/upper sums.  Every positive rational request returns a certified finite
subdivision with smaller oscillation.  This is the operational content of
integrability used here; no limiting integral value is constructed.
-/

namespace Purelib.Integration

set_option genInjectivity false in
open Purelib in
open Purelib.Data.Rat in
/-- A stateful finite-cell integration refinement that answers every positive width request.

Each state retains its exact frontier; requests certify frontier refinement and weighted oscillation below the supplied
tolerance, with all states refining the initial frontier. -/
structure IntegrationProcess (α : Type) where
  /-- The retained state type of the integration refinement. -/ State : Type
  /-- The exact ordered integration cells retained at each state. -/ frontier : State → List
    (Integration.IntegrationCell α)
  /-- The initial state of the original integration process. -/ initial : State
  /-- Refine the supplied state for a strictly positive rational tolerance. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- The requested frontier refines the exact input frontier. -/ request_refines : ∀ state epsilon positive,
    Integration.IntegrationFrontierRefines
      (frontier (request state epsilon positive)) (frontier state)
  /-- The requested frontier's weighted oscillation is below the supplied tolerance. -/ accurate : ∀ state epsilon
    positive,
    Integration.integralOscillation (frontier (request state epsilon positive)) < epsilon
  /-- Every state's frontier refines the original initial frontier. -/ refinesInitial : ∀ state,
    Integration.IntegrationFrontierRefines (frontier state) (frontier initial)

constructive_injectivity IntegrationProcess

namespace IntegrationProcess

open Purelib in
/-- Read the same states and requests as an interval process using each frontier's integral enclosure. -/
def toBoundProcess {α : Type} (process : Integration.IntegrationProcess α) :
    Approximation.BoundProcess where
  State := process.State
  bound state := Integration.integralBound (process.frontier state)
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).integralBound_refines
  accurate state epsilon positive := by
    rw [Integration.integralBound_width]
    exact process.accurate state epsilon positive
  refinesInitial state :=
    (process.refinesInitial state).integralBound_refines

section
open Purelib
open Purelib.Data.Rat
/-- A width request cannot decrease the retained frontier's lower integral. -/
theorem request_lower_mono {α : Type} (process : Integration.IntegrationProcess α)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Integration.lowerIntegral (process.frontier state) ≤
      Integration.lowerIntegral (process.frontier
        (process.request state epsilon positive)) :=
  (process.toBoundProcess.lowerRequestProcess epsilon positive).monotone state

/-- A width request cannot increase the retained frontier's upper integral. -/
theorem request_upper_antitone {α : Type} (process : Integration.IntegrationProcess α)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Integration.upperIntegral (process.frontier
      (process.request state epsilon positive)) ≤
        Integration.upperIntegral (process.frontier state) :=
  (process.toBoundProcess.upperRequestProcess epsilon positive).antitone state

/-- The requested frontier's integral enclosure is narrower than the positive tolerance. -/
theorem request_width_lt {α : Type} (process : Integration.IntegrationProcess α)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (Integration.integralBound (process.frontier
      (process.request state epsilon positive))).width < epsilon := by
  rw [Integration.integralBound_width]
  exact process.accurate state epsilon positive

end

section
open Purelib
/-- Run the retained ordered list of positive accuracy requests from the supplied original state. -/
def runRequests {α : Type} (process : Integration.IntegrationProcess α)
    (state : process.State) (requests : List Approximation.AccuracyRequest) : process.State :=
  process.toBoundProcess.runRequests state requests

/-- The final frontier after a request list meets every tolerance occurring in that list. -/
theorem runRequests_oscillation_lt_of_mem {α : Type}
    (process : Integration.IntegrationProcess α) (state : process.State)
    (requests : List Approximation.AccuracyRequest) (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) :
    Integration.integralOscillation
      (process.frontier (process.runRequests state requests)) <
        request.tolerance := by
  have accurate := process.toBoundProcess.runRequests_width_lt_of_mem
    state requests request member
  change (Integration.integralBound (process.frontier
    (process.runRequests state requests))).width < request.tolerance at accurate
  rw [Integration.integralBound_width] at accurate
  exact accurate

end

open Purelib in
open Purelib.Data.Rat in
open Purelib.Integration in
/-- Build a constant-state integration process from exact weighted payload-value occurrences.

The original list becomes a zero-oscillation frontier, so every positive accuracy request returns the same unit state.
-/
def exactSimple {α : Type}
    (entries : List (Measure.Weighted (α × Fraction.Rational))) : Integration.IntegrationProcess α where
  State := Unit
  frontier _ := entries.map fun entry =>
    IntegrationCell.exact entry.item.1 entry.weight entry.item.2
      entry.nonnegative
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive := IntegrationFrontierRefines.refl _
  accurate state epsilon positive := by
    have exactWidth := Integration.integralBound_exact_width entries
    rw [Integration.integralBound_width] at exactWidth
    rw [exactWidth]
    exact positive
  refinesInitial state := IntegrationFrontierRefines.refl _

end IntegrationProcess

end Purelib.Integration
