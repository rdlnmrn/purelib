module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Program
import Purelib.Computation.Query.Iteration
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
public import Purelib.Data.CCL.Transducer.Replay.Machine.Consume
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Controller
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Computation.Query.Replay

/-!
# Finite numerical controller and adaptive replay

The finite query construction consumes retained pending bits before querying
the shared controller. Failures stop subsequent finite steps. Both ordinary
replay and expanded model reads compile or substitute this same construction.
-/

@[expose] public section

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Machine

open Purelib.CCL.Progressive
open Purelib.Computation.Query (Program Protocol)
open Purelib.Data.CCL.Transducer
open Purelib.Integration.Program.Gaussian.CCL.Replay

/-- Construct the next pending-bit emission or one controller emission when the retained queue is empty.

The original mode and emitted prefix remain fixed until the same checked
controller result is consumed. Explicit failures retain their original boundary.
-/
def nextBitProgram (control : IntegrationReplay.Control) (machine : Replay.Machine) :
    IntegrationReplay.QueryProgram (Except Replay.Failure Replay.Machine) :=
  match machine.pending with
  | bit :: rest => .pure (.ok ⟨machine.mode, machine.emitted ++ [bit], rest⟩)
  | [] => (Controller.stepProgram control machine.mode).map fun result =>
      result.bind (Replay.Machine.Consume.consume machine.emitted)

/-- Execute the shared next-bit construction, consuming the actual retained pending queue. -/
def nextBit (control : IntegrationReplay.Control) (machine : Replay.Machine) :
    IntegrationReplay.QueryComputation (Except Replay.Failure Replay.Machine) :=
  (nextBitProgram control machine).protocol

/-- Next-bit execution retains the exact queue, controller result and complete ordered model-query log. -/
theorem nextBit_run (control : IntegrationReplay.Control) (machine : Replay.Machine)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    (nextBit control machine).run oracle =
      ((match machine.pending with
      | bit :: rest => .pure (.ok ⟨machine.mode, machine.emitted ++ [bit], rest⟩)
      | [] => (Controller.step control machine.mode).map fun result =>
          result.bind (Replay.Machine.Consume.consume machine.emitted)) :
        IntegrationReplay.QueryComputation (Except Replay.Failure Replay.Machine)).run oracle := by
  unfold nextBit nextBitProgram
  cases machine.pending with
  | cons bit rest => rfl
  | nil => exact Program.map_execution _ _ oracle

/-- Construct the displayed finite advance, preserving encountered failure and the same pending-bit steps. -/
def advanceProgram (control : IntegrationReplay.Control) (machine : Replay.Machine) (count : Nat) :
    IntegrationReplay.QueryProgram (Except Replay.Failure Replay.Machine) :=
  Program.iterate (fun result =>
    match result with
    | .error error => .pure (.error error)
    | .ok current => nextBitProgram control current) count (.ok machine)

/-- Execute the shared finite machine advance construction. -/
def advance (control : IntegrationReplay.Control) (machine : Replay.Machine) (count : Nat) :
    IntegrationReplay.QueryComputation (Except Replay.Failure Replay.Machine) :=
  (advanceProgram control machine count).protocol

/-- Finite advance execution preserves every actual bit step, explicit failure and complete ordered model-query log. -/
theorem advance_run (control : IntegrationReplay.Control) (machine : Replay.Machine) (count : Nat)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    (advance control machine count).run oracle =
      (Protocol.iterate (fun result =>
        match result with
        | .error error => .pure (.error error)
        | .ok current => nextBit control current) count (.ok machine)).run oracle := by
  rewrite [advance, advanceProgram, Program.iterate_execution]
  apply Protocol.iterate_execution_eq _ _ _ _ oracle
  intro result
  cases result <;> rfl

/-- Replaying the exact recorded query trace recovers the original finite advance result. -/
theorem advance_replay (control : IntegrationReplay.Control) (machine : Replay.Machine) (count : Nat)
    (oracle : Nat → IntegrationReplay.CachedModel) :
    (advance control machine count).replayExact ((advance control machine count).run oracle).trace =
      .ok ((advance control machine count).run oracle).value :=
  Protocol.replayExact_run _ _

/-- An oracle agreeing with every retained reply produces the same finite advance result and query trace. -/
theorem advance_run_of_answers (control : IntegrationReplay.Control) (machine : Replay.Machine) (count : Nat)
    (first second : Nat → IntegrationReplay.CachedModel)
    (agrees : Purelib.Computation.Query.Basic.Answers second ((advance control machine count).run first).trace) :
    (advance control machine count).run second = (advance control machine count).run first :=
  Protocol.run_of_answers _ first second agrees

namespace ReplayController

/-- A successful initial advance followed by extra steps equals advancing by their sum with the two exact logs appended.

The success equation retains the actual first resulting machine. Further
iteration consumes that same state and concatenates only its new queries.
-/
theorem advance_run_add_of_ok (control : IntegrationReplay.Control) (machine next : Replay.Machine)
    (first extra : Nat) (oracle : Nat → IntegrationReplay.CachedModel)
    (success : ((advance control machine first).run oracle).value = .ok next) :
    (advance control machine (first + extra)).run oracle =
      let after := (advance control next extra).run oracle
      ⟨after.value, ((advance control machine first).run oracle).trace ++ after.trace⟩ := by
  rewrite [advance_run control machine first oracle] at success
  rewrite [advance_run control machine (first + extra) oracle,
    advance_run control next extra oracle, advance_run control machine first oracle]
  rw [Protocol.iterate_run_add]
  dsimp only
  rewrite [success]
  exact Eq.refl _

end ReplayController

end Purelib.Integration.Program.Gaussian.CCL.Replay.Machine
