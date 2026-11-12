module

public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Computation.Query.Program

/-!
# Expanding integration model reads into their actual internal protocols

The same finite controller, charts and pending bits determine model reads.
An expanded handler supplies each exact cached model once, through its own
protocol. The result retains the original complete integration execution;
the expanded trace contains the handler requests in actual execution order.
Replay consumes those same replies without consulting the internal oracle.
-/

public section

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Data.CCL.Transducer
open Purelib.Integration.CertifiedProgram (Request)
open Purelib.Computation
open Purelib.Computation.Query

namespace Expansion

/-- The original integration query construction, retaining its actual cached-model reply carrier. -/
abbrev Construction (Value : Type) := Query.Program Nat CachedModel Value

/-- Retain the shared observation construction at its original operation owner. -/
def program (control : Control) (request : Request) (count : Nat) :
    Construction (Except Replay.Failure Observation) := Basic.computationProgram control request count

/-- The retained construction compiles to the same complete integration observation execution. -/
theorem program_execution (control : Control) (request : Request) (count : Nat) (oracle : Nat → CachedModel) :
    (program control request count).protocol.run oracle = (Basic.computation control request count).run oracle := by
  rewrite [program]
  rfl

/-- Replace model reads by their internal protocols, retaining the complete original execution as the returned value. -/
def computation {Question Reply : Type} (handlers : Nat → Protocol Question Reply CachedModel)
    (control : Control) (request : Request) (count : Nat) :
    Protocol Question Reply (Computation.Query.Basic.Execution Nat CachedModel (Except Replay.Failure Observation)) :=
  (program control request count).expand handlers

/-- The expanded run retains the exact original observation and every original cached-model query. -/
theorem computation_value {Question Reply : Type} (handlers : Nat → Protocol Question Reply CachedModel)
    (control : Control) (request : Request) (count : Nat) (oracle : Question → Reply) :
    ((computation handlers control request count).run oracle).value =
      (Basic.computation control request count).run (fun index => ((handlers index).run oracle).value) :=
  (Query.Program.expand_value handlers (program control request count) oracle).trans
    (program_execution control request count _)

/-- Replay from the inner trace returns the original complete observation execution and outer model log. -/
theorem computation_replay {Question Reply : Type} (handlers : Nat → Protocol Question Reply CachedModel)
    (control : Control) (request : Request) (count : Nat) (oracle : Question → Reply) :
    (computation handlers control request count).replayExact
      ((computation handlers control request count).run oracle).trace =
      .ok ((Basic.computation control request count).run (fun index => ((handlers index).run oracle).value)) :=
  ((computation handlers control request count).replayExact_run oracle).trans
    (congrArg Except.ok (computation_value handlers control request count oracle))

/-- Outside-inner-trace payload changes preserve the observation, original model log and complete inner request log. -/
theorem payload_erasure {Question Reply Payload : Type} [DecidableEq Question]
    (handlers : Nat → Protocol Question Reply CachedModel) (control : Control) (request : Request) (count : Nat)
    (oracle : Question → Reply) (payload : Payload) (outside : Payload → Question → Reply) :
    let computation := computation handlers control request count
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (computation handlers control request count) oracle payload outside

end Expansion

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
