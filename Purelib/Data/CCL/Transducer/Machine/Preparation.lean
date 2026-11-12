module

public import Purelib.Data.CCL.Transducer.Machine.Step
public import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Mode.Observation
public import Purelib.Approximation.Gaussian.Process.Route
import Purelib.Approximation.Gaussian.Process.Route.Request
import Purelib.Data.CCL.Transducer.Emission.Step

/-!
# Retained productive bit preparation

The original pending-result selector and emission preparation produce one
actual returned bit and machine. Its same next source route and observation
are retained, so downstream frame and history construction reuse that work.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine.Step

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer

set_option genInjectivity false in
/-- One actual original bit result with its cached next observation and paid original source calls. -/
structure Prepared (source : Process) (machine : Machine) where
  /-- The original returned bit and next machine, computed once. -/ result : Bool × Machine
  /-- The same complete result is the original next-bit procedure's result. -/ resultEq : result = nextBit machine
  /-- The same original supplied process is retained through the actual next chart. -/ route :
    Process.Route source result.2.mode.process
  /-- The exact original next-mode ball and witness, retained without rereading the source. -/ observation :
    Mode.Observation result.2.mode
  /-- The actual source-interface calls made by this finite bit transition. -/ sourceCalls : Nat

/-- Consume the same retained original emission once when the original pending queue is empty.

The emission's complete result supplies the next route, observation and source
payment. No preparation, refinement or source observation is performed here.
-/
@[expose] def fromEmission {source : Process} (machine : Machine)
    (empty : pendingResult machine = none) (prepared : Emission.Prepared source)
    (same : prepared.emission = Emission.Step.step machine.mode) : Prepared source machine :=
  let result := consumeEmission machine.emitted prepared.emission
  have modeEq : result.2.mode = prepared.emission.next :=
    Committed.consumeEmission_mode machine.emitted prepared.emission
  { result := result
    resultEq := by
      unfold nextBit
      rewrite [empty]
      exact congrArg (consumeEmission machine.emitted) same
    route := (congrArg Mode.process modeEq).symm ▸ prepared.route
    observation := modeEq.symm ▸ prepared.observation
    sourceCalls := prepared.sourceCalls }

/-- Prepare one original pending or newly emitted bit while retaining its actual observation and payment.

A queued bit transports the exact old cache and pays zero source calls. An
empty queue prepares one original emission, consumes that exact retained
chunk once and transports its same already computed next observation.
-/
@[expose] def prepare {source : Process} (machine : Machine)
    (route : Process.Route source machine.mode.process) (observation : Mode.Observation machine.mode) :
    Prepared source machine :=
  match pendingEq : pendingResult machine with
  | some result =>
      have modeEq := pendingResult_mode machine result pendingEq
      { result := result
        resultEq := by unfold nextBit; rewrite [pendingEq]; rfl
        route := (congrArg Mode.process modeEq).symm ▸ route
        observation := modeEq.symm ▸ observation
        sourceCalls := 0 }
  | none =>
      let prepared := Emission.Step.prepare machine.mode route
      fromEmission machine pendingEq prepared (Emission.Step.prepare_emission_eq machine.mode route)

/-- The prepared bit result preserves the complete original bit, machine, emitted word and pending queue. -/
theorem prepare_result_eq {source : Process} (machine : Machine)
    (route : Process.Route source machine.mode.process) (observation : Mode.Observation machine.mode) :
    (prepare machine route observation).result = nextBit machine := (prepare machine route observation).resultEq

/-- A prepared queued-bit transition performs no source refinement, ball read or witness read. -/
theorem prepare_sourceCalls_of_pending {source : Process} (machine : Machine)
    (route : Process.Route source machine.mode.process) (observation : Mode.Observation machine.mode)
    (nonempty : machine.pending ≠ []) : (prepare machine route observation).sourceCalls = 0 := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil => exact (nonempty rfl).elim
      | cons bit rest => rfl

/-- A prepared bit transition pays zero, three or seven actual supplied-source interface calls. -/
theorem prepare_sourceCalls {source : Process} (machine : Machine)
    (route : Process.Route source machine.mode.process) (observation : Mode.Observation machine.mode) :
    (prepare machine route observation).sourceCalls = 0 ∨
      (prepare machine route observation).sourceCalls = 3 ∨
        (prepare machine route observation).sourceCalls = 7 := by
  unfold prepare
  split
  · exact Or.inl rfl
  · exact Or.inr (Emission.Step.prepare_sourceCalls machine.mode route)

/-- Prepare the same original returned bit through exact source handlers and the retained emission constructor.

A pending bit consumes the old observation and makes no handler call. An empty
queue handles the original emission requests, then consumes that same chunk
once. The continuation retains the complete original bit preparation, including
the unchanged next machine, route, observation and source payment.
-/
def withPreparation {m : Type → Type} [Monad m] {source : Process} {α : Type}
    (stateHandler : Process.Route.StateHandler m source) (handler : Process.Route.Handler m source)
    (machine : Machine) (route : Process.Route source machine.mode.process)
    (observation : Mode.Observation machine.mode)
    (use : (prepared : Prepared source machine) → prepared = prepare machine route observation → m α) : m α :=
  match pendingEq : pendingResult machine with
  | some _ => use (prepare machine route observation) rfl
  | none =>
      Emission.Step.withPreparation stateHandler handler machine.mode route fun emission same =>
        let prepared := fromEmission machine pendingEq emission
          ((congrArg Emission.Prepared.emission same).trans (Emission.Step.prepare_emission_eq machine.mode route))
        use prepared (by
          unfold prepare
          split
          · rename_i result queued
            cases (queued.symm.trans pendingEq)
          · cases same
            rfl)

end Purelib.Data.CCL.Transducer.Machine.Step
