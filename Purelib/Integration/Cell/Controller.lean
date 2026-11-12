module
public import Purelib.Integration.Cell.Process
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Persistent histories of finite integration refinements

A controller retains its original initial result and actual continuation
objects. Its finite history is indexed by the exact latest frontier; each
continuation supplies its own original request, split proof and accuracy.
-/

public section

namespace Purelib.Integration

open Purelib.Approximation
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A finite integration controller with actual request-specific continuations.

The frontier and its original cells are supplied by the client. Each step is
the client's retained continuation object, not a reconstructed proof-only
view. Its exact request, cell split and finite width law drive the shared
persistent integration process. -/
structure RefiningController (Frontier α : Type) (cells : Frontier → List (IntegrationCell α)) where
  /-- The original initial result type. -/ Output : Type
  /-- The actual initial result retained by this controller. -/ origin : Output
  /-- Read a frontier from the original initial result. -/ frontier : Output → Frontier
  /-- Actual continuation objects indexed by their saved previous frontier. -/ Step : Frontier → Type
  /-- Read the new frontier from the actual retained continuation. -/ next :
    {previous : Frontier} → Step previous → Frontier
  /-- Read the original positive request from the actual continuation. -/ stepRequest :
    {previous : Frontier} → Step previous → AccuracyRequest
  /-- Continue the exact saved frontier with one new positive request. -/ advance :
    (previous : Frontier) → AccuracyRequest → Step previous
  /-- The continuation retains the supplied request. -/ advance_request : ∀ previous request,
    stepRequest (advance previous request) = request
  /-- Every actual continuation is an original finite cell-split refinement. -/ step_refines :
    ∀ {previous} (step : Step previous), IntegrationFrontierRefines (cells (next step)) (cells previous)
  /-- Every actual continuation meets its own retained positive width request. -/ step_accurate :
    ∀ {previous} (step : Step previous), (integralBound (cells (next step))).width < (stepRequest step).tolerance

constructive_injectivity RefiningController

namespace RefiningController

set_option genInjectivity false in
/-- A finite history indexed by the controller's exact latest retained frontier.

Each step stores the actual client continuation, including its original
request and cached data. The initial history retains the original result as
its index; no new source or replay representation is introduced. -/
inductive History {Frontier α : Type} {cells : Frontier → List (IntegrationCell α)}
    (controller : RefiningController Frontier α cells) (origin : controller.Output) : Frontier → Type where
  /-- Start from the original retained result. -/ | initial : History controller origin (controller.frontier origin)
  /-- Append one actual continuation of the exact previous frontier. -/ | next {previous : Frontier} :
      History controller origin previous → (step : controller.Step previous) →
        History controller origin (controller.next step)

constructive_injectivity History

namespace History

/-- The latest original frontier and its finite indexed continuation history. -/
abbrev State {Frontier α : Type} {cells : Frontier → List (IntegrationCell α)}
    (controller : RefiningController Frontier α cells) (origin : controller.Output) :=
  Σ frontier : Frontier, History controller origin frontier

/-- Every historical frontier is a finite split refinement of its original frontier. -/
theorem frontier_refines_origin {Frontier α : Type} {cells : Frontier → List (IntegrationCell α)}
    {controller : RefiningController Frontier α cells} {origin : controller.Output} {frontier : Frontier}
    (history : History controller origin frontier) :
    IntegrationFrontierRefines (cells frontier) (cells (controller.frontier origin)) := by
  induction history with
  | initial => exact .refl _
  | next previous step inductionHypothesis => exact .trans (controller.step_refines step) inductionHypothesis

/-- Every historical integral enclosure refines the exact original enclosure. -/
theorem refines_origin {Frontier α : Type} {cells : Frontier → List (IntegrationCell α)}
    {controller : RefiningController Frontier α cells} {origin : controller.Output} {frontier : Frontier}
    (history : History controller origin frontier) :
    Purelib.Data.Rat.Interval.Refines (integralBound (cells frontier))
      (integralBound (cells (controller.frontier origin))) :=
  history.frontier_refines_origin.integralBound_refines

end History

/-- Construct an integration process whose continuation may consume its exact finite history.

The selected continuation still retains the current frontier as its original
index and must retain the supplied request. Earlier continuation objects stay
available to the executable selector. -/
@[expose] def integrationProcessWith {Frontier α : Type} {cells : Frontier → List (IntegrationCell α)}
    (controller : RefiningController Frontier α cells)
    (advance : (state : History.State controller controller.origin) →
      AccuracyRequest → controller.Step state.1)
    (advance_request : ∀ state request, controller.stepRequest (advance state request) = request) :
    IntegrationProcess α := by
  let State := History.State controller controller.origin
  let initial : State := ⟨controller.frontier controller.origin, History.initial⟩
  let request : (state : State) → (epsilon : Fraction.Rational) → 0 < epsilon → State := fun state epsilon positive =>
    let step := advance state ⟨epsilon, positive⟩
    ⟨controller.next step, History.next state.2 step⟩
  exact
    { State := State
      frontier := fun state => cells state.1
      initial := initial
      request := request
      request_refines := by
        intro state epsilon positive
        exact controller.step_refines (advance state ⟨epsilon, positive⟩)
      accurate := by
        intro state epsilon positive
        have accuracy := controller.step_accurate (advance state ⟨epsilon, positive⟩)
        rw [advance_request] at accuracy
        rw [integralBound_width] at accuracy
        exact accuracy
      refinesInitial := by
        intro state
        exact state.2.frontier_refines_origin }

/-- Construct the original integration process from actual finite controller continuations. -/
@[expose] def integrationProcess {Frontier α : Type} {cells : Frontier → List (IntegrationCell α)}
    (controller : RefiningController Frontier α cells) : IntegrationProcess α :=
  controller.integrationProcessWith (fun state request => controller.advance state.1 request)
    (fun state request => controller.advance_request state.1 request)

end RefiningController

end Purelib.Integration

end
