module
import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Loop
public import Purelib.Data.CCL.Transducer.Emission.Low
public import Purelib.Data.CCL.Transducer.Emission.Residual
import Purelib.Data.CCL.Transducer.Mode.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Approximation.Gaussian.Process.Route.Request
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Rat.Fraction.Order.Field

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Step

open Purelib.Data.CCL.Transducer in
/-- Dispatch the retained transducer mode to its exact certified nonempty emission procedure.

Initial, low, loop and residual cases keep their original dependent state records and use the corresponding constructor
without changing its selected witnesses or next process owner. -/
def step : Data.CCL.Transducer.Mode → Data.CCL.Transducer.Emission
  | .initial current => Emission.Initial.initialStep current
  | .low current => Emission.Low.lowStep current
  | .loop current => Emission.Loop.loopStep current
  | .residual current => Emission.Residual.residualStep current

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer

/-- Prepare the original selected emission once with its same source route, cached observation and payment. -/
def prepare {source : Process} : (mode : Mode) →
    Process.Route source mode.process → Emission.Prepared source
  | .initial current, route => Emission.Initial.prepare current route
  | .low current, route => Emission.Low.prepare current route
  | .loop current, route => Emission.Loop.prepare current route
  | .residual current, route => Emission.Residual.prepare current route

/-- Routed preparation retains the complete original selected emission for every productive mode. -/
theorem prepare_emission_eq {source : Process} (mode : Mode) (route : Process.Route source mode.process) :
    (prepare mode route).emission = step mode := by
  cases mode with
  | initial current => exact Emission.Initial.prepare_emission_eq current route
  | low current => exact Emission.Low.prepare_emission_eq current route
  | loop current => exact Emission.Loop.prepare_emission_eq current route
  | residual current => exact Emission.Residual.prepare_emission_eq current route

/-- Every actual emission pays three source calls or the seven-call residual inverse transition. -/
theorem prepare_sourceCalls {source : Process} (mode : Mode) (route : Process.Route source mode.process) :
    (prepare mode route).sourceCalls = 3 ∨ (prepare mode route).sourceCalls = 7 := by
  cases mode with
  | initial current => exact Or.inl (Emission.Initial.prepare_sourceCalls current route)
  | low current => exact Or.inl (Emission.Low.prepare_sourceCalls current route)
  | loop current => exact Or.inl (Emission.Loop.prepare_sourceCalls current route)
  | residual current => exact Emission.Residual.prepare_sourceCalls current route

end Purelib.Data.CCL.Transducer.Emission.Step

end

namespace Purelib.Data.CCL.Transducer.Emission.Step

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat

variable {m : Type → Type} [Monad m] {source : Process} {α : Type}
variable (stateHandler : Process.Route.StateHandler m source) (handler : Process.Route.Handler m source)

/-- Prepare the original initial branch from one handled source refinement. -/
private def withInitial (current : Mode.Basic.InitialState) (route : Process.Route source current.process)
    (use : (prepared : Emission.Prepared source) → prepared = Initial.prepare current route → m α) : m α := do
  let receipt ← route.refineWith handler current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  let prepared := Initial.fromRefinement current route receipt
  use { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }
    (Initial.prepare_eq_fromRefinement current route receipt).symm

/-- Prepare the original low branch from its same handled source request. -/
private def withLow (current : Mode.Basic.LowState) (route : Process.Route source current.process)
    (use : (prepared : Emission.Prepared source) → prepared = Low.prepare current route → m α) : m α := do
  let receipt ← route.refineWith handler current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  let prepared := Low.fromRefinement current route receipt
  use { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }
    (Low.prepare_eq_fromRefinement current route receipt).symm

/-- Prepare the original loop branch from its same handled domain request. -/
private def withLoop (current : Mode.Basic.LoopState) (route : Process.Route source current.process)
    (use : (prepared : Emission.Prepared source) → prepared = Loop.prepare current route → m α) : m α := do
  let receipt ← route.refineWith handler current.state current.domain.decisionTarget current.domain.decisionTarget_pos
  let prepared := Loop.fromRefinement current route receipt
  use { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }
    (Loop.prepare_eq_fromRefinement current route receipt).symm

/-- Handle the original padding decision and the distinct state-only inverse setup when required. -/
private def withResidual (current : Mode.Basic.ResidualState) (route : Process.Route source current.process)
    (use : (prepared : Emission.Prepared source) → prepared = Residual.prepare current route → m α) : m α := do
  let target := Padding.Residual.paddingTarget (current.count + 1)
  have positive := Fraction.Order.Field.div_pos_direct (Padding.Residual.paddingTarget_pos (current.count + 1))
    (show (0 : Fraction.Rational) < 6 by decide)
  let receipt ← route.refineWith handler current.state (target / 6) positive
  have persists : ∀ {value}, current.process.Possible receipt.state value →
      current.process.Possible current.state value :=
    fun possible => current.process.refine_persists current.state (target / 6) positive (receipt.stateEq ▸ possible)
  let selected := Residual.selectionOfRefinement current route positive receipt
  have fresh : Residual.prepare current route =
      let prepared := Residual.Selection.prepare current route receipt.state receipt.observation persists selected
      { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls } :=
    Residual.prepare_eq_fromRefinement current route positive receipt
  match selectedEq : selected with
  | .small certificate =>
      let prepared := Residual.Selection.prepare current route receipt.state receipt.observation persists
        (.small certificate)
      use { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls } (by
        rewrite [selectedEq] at fresh
        exact fresh.symm)
  | .apart certificate =>
      let original := receipt.observation.ballEq ▸ certificate
      let apart := Process.Apart.Based.possibleApartOfBall current.process receipt.state original
      let retained ← route.refineStateWith stateHandler receipt.state (apart.lowerSq / 12) apart.twelfth_pos
      let next := Residual.apartLoopStateOfRefinement current receipt.state persists original retained
      let inverseRoute : Process.Route source next.val.process :=
        (congrArg Mode.Basic.LoopState.process next.property).symm ▸
          (.inverse route receipt.state original current.count)
      withLoop handler next.val inverseRoute fun nested same => do
        let prepared : Emission.Prepared source :=
          ⟨nested.emission, nested.route, nested.observation,
            receipt.sourceCalls + (route.calls + nested.sourceCalls)⟩
        use prepared (by
          have transfer : ∀ (state : Mode.Basic.LoopState)
              (stateEq : state = Residual.apartLoopState current receipt.state persists original)
              (value : Emission.Prepared source),
              value = Loop.prepare state ((congrArg Mode.Basic.LoopState.process stateEq).symm ▸
                (.inverse route receipt.state original current.count)) →
              value = Loop.prepare (Residual.apartLoopState current receipt.state persists original)
                (.inverse route receipt.state original current.count) := by
            intro state stateEq value valueEq
            cases stateEq
            exact valueEq
          have nestedEq : nested = Loop.prepare (Residual.apartLoopState current receipt.state persists original)
              (.inverse route receipt.state original current.count) := transfer next.val next.property nested same
          rewrite [selectedEq] at fresh
          dsimp only [prepared]
          rewrite [nestedEq]
          exact fresh.symm)

/-- Prepare one complete original emission through supplied exact source handlers.

The observed handler supplies one retained state, ball and witness for each
original decision request. Inverse setup uses the separate state-only handler
at its unchanged target. The continuation receives the complete original
preparation, including its nominal next route and exact source-call payment.
-/
public def withPreparation (mode : Mode) (route : Process.Route source mode.process)
    (use : (prepared : Emission.Prepared source) → prepared = prepare mode route → m α) : m α :=
  match mode with
  | .initial current => withInitial handler current route use
  | .low current => withLow handler current route use
  | .loop current => withLoop handler current route use
  | .residual current => withResidual stateHandler handler current route use

end Purelib.Data.CCL.Transducer.Emission.Step
