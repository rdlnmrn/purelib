module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Integration.Program.Gaussian.CCL.Replay.Machine
import Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Representation
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Computation.Query.Replay
import Purelib.Integration.Program.Gaussian.Cached.Basic

/-!
# Retained observation continuation

Continuation reuses the retained selected reading, replay machine and
pending bits. The new receipt stores only newly consumed replies; joining
it with the original receipt gives the same complete uninterrupted observation.
-/

section

open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Integration.CertifiedProgram (Request InvalidRequest)
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Computation.Query
open Purelib.Data.CCL.Transducer
open Purelib.Approximation.Gaussian
open Purelib.Integration.Program.Gaussian.CCL.Replay (Observation)

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

/-- Advance the saved replay machine for the extra bit count while retaining its exact original selected reading.

The retained selected reading is reused, and the existing saved
machine advances for exactly the supplied additional bit count. -/
@[expose] public def IntegrationReplay.resumeComputation (control : Control) (saved : Observation)
  (extra : Nat) :
    QueryComputation (Except Data.CCL.Transducer.Replay.Failure Observation) :=
  (Machine.advance control saved.machine extra).map fun result =>
    result.map fun machine => ⟨saved.selected, machine⟩

/-- Resuming for zero steps returns the original saved observation with no queries.

Zero additional bits invoke no source query and retain the exact
selected reading, machine and empty new transcript. -/
public theorem IntegrationReplay.resume_zero_run (control : Control) (saved : Observation) (oracle :
  Nat → CachedModel) :
    (IntegrationReplay.resumeComputation control saved 0).run oracle = ⟨.ok saved, []⟩ := rfl

/-- A pending bit is emitted from the saved buffer without querying the source or replacing the selected reading.

The supplied pending-bit equation identifies the original buffer.
Its head is appended to the emitted word while the retained tail remains pending. -/
public theorem IntegrationReplay.resume_buffered_one_run (control : Control) (saved : Observation)
    (bit : Bool) (rest : List Bool) (buffered : saved.machine.pending = bit :: rest)
    (oracle : Nat → CachedModel) :
    (IntegrationReplay.resumeComputation control saved 1).run oracle =
      ⟨.ok ⟨saved.selected, ⟨saved.machine.mode, saved.machine.emitted ++ [bit], rest⟩⟩, []⟩ := by
  cases saved with
  | mk selected machine =>
      cases machine with
      | mk mode emitted pending =>
          change pending = bit :: rest at buffered
          cases buffered
          rfl

/-- Split the original observation execution into its selected-stage exchange and exact machine-prefix execution.

The original request contributes its selected-stage exchange before
the unchanged machine-prefix value and ordered trace. -/
private theorem IntegrationReplay.computation_run (program : CachedProgram) (request : Request) (count : Nat) :
    (Observation.Basic.computation (control program) request count).run program.stage =
      let prefixExecution := (Machine.advance (control program)
        (.initial (selectedIndex (control program) request)) count).run program.stage
      ⟨prefixExecution.value.map (fun machine => ⟨requestedReading program request, machine⟩),
        ⟨selectedIndex (control program) request, program.stage (selectedIndex (control program) request)⟩ ::
          prefixExecution.trace⟩ := by
  change Basic.Execution.mk
    ((Observation.Basic.computation (control program) request count).run program.stage).value
    ((Observation.Basic.computation (control program) request count).run program.stage).trace = _
  rw [Observation.Representation.computation_trace, Observation.Basic.computation,
    Computation.Query.Protocol.bind_run_value,
    requestReading, read_stage_value, Observation.Basic.continueObservation, Computation.Query.Protocol.map_run_value]
  rfl

/-- Resuming the saved observation equals the full longer execution with the original and resumed transcripts appended.

The saved machine and selected reading are reused; the equation identifies the exact value and ordered query history. -/
public theorem IntegrationReplay.resume_execution (program : CachedProgram) (request : Request) (count extra : Nat)
    (saved : Observation.Record.Recorded program request count) :
    (Observation.Basic.computation (control program) request (count + extra)).run program.stage =
      let after := (IntegrationReplay.resumeComputation (control program) saved.observation extra).run program.stage
      ⟨after.value, saved.trace ++ after.trace⟩ := by
  obtain ⟨machine, success, _⟩ := MachineProjection.initial_advance_rep
    program (selectedIndex (control program) request) count
  have before := IntegrationReplay.computation_run program request count
  dsimp only at before
  rewrite [success, Except.map] at before
  have observation_eq : saved.observation = ⟨requestedReading program request, machine⟩ :=
    Except.ok.inj (saved.value_eq.symm.trans (congrArg Basic.Execution.value before))
  have trace_eq := saved.trace_eq.trans (congrArg Basic.Execution.trace before)
  rw [IntegrationReplay.computation_run, Machine.ReplayController.advance_run_add_of_ok _ _ _ _ extra _ success,
    observation_eq, trace_eq]
  rewrite [IntegrationReplay.resumeComputation]
  dsimp only
  rewrite [Computation.Query.Protocol.map_run_value,
    Computation.Query.Protocol.map_run_trace, List.cons_append]
  exact Eq.refl _

@[expose] public section

set_option genInjectivity false in
/-- The exact resumed observation and new transcript indexed by the original saved record and extra bit count.

The original successful continuation and trace equations bind both fields
to that same saved machine, selected reading and additional bit count. -/
structure IntegrationReplay.Resumed {program : CachedProgram} {request : Request} {count : Nat}
    (saved : Observation.Record.Recorded program request count) (extra : Nat) where
  /-- The retained successful observation after the exact saved-machine continuation. -/ observation :
    Observation
  /-- The retained new query transcript from resuming the original saved machine. -/ trace : Trace
  /-- The exact saved-machine continuation returns this retained successful observation. -/ value_eq :
    ((IntegrationReplay.resumeComputation (control program) saved.observation extra).run program.stage).value =
    .ok observation
  /-- The retained new transcript equals the exact saved-machine continuation trace. -/ trace_eq : trace =
    ((IntegrationReplay.resumeComputation (control program) saved.observation extra).run program.stage).trace

constructive_injectivity IntegrationReplay.Resumed

end

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

/-- Run the saved observation's exact machine continuation once and retain its successful value and new transcript.

The continuation uses the original selected reading and saved machine. Its
success and trace equations retain the exact result of that single execution. -/
@[expose] public def Recorded.resume {program : CachedProgram} {request : Request} {count : Nat}
    (saved : Observation.Record.Recorded program request count) (extra : Nat) :
      Observation.Resume.IntegrationReplay.Resumed saved extra :=
  let execution := (Observation.Resume.IntegrationReplay.resumeComputation (control program) saved.observation
    extra).run program.stage
  match result : execution.value with
  | .ok observation =>
      ⟨observation, execution.trace, result, rfl⟩
  | .error error => by
      have impossible : False := by
        obtain ⟨machine, success, _⟩ := MachineProjection.advance_rep extra saved.rep.2
        have successful : execution.value = .ok ⟨saved.observation.selected, machine⟩ := by
          change ((Observation.Resume.IntegrationReplay.resumeComputation (control program) saved.observation extra).run
            program.stage).value = _
          rw [Observation.Resume.IntegrationReplay.resumeComputation, Computation.Query.Protocol.map_run_value, success]
          rfl
        have unequal := result.symm.trans successful
        nomatch unequal
      nomatch impossible

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

/-- Combine the original and resumed transcripts into a certified record of the full longer observation.

The exact new observation is retained, and the original saved trace
is concatenated with the new trace in execution order. -/
@[expose] public def IntegrationReplay.Resumed.recorded {program : CachedProgram} {request : Request} {count extra :
  Nat}
    {saved : Observation.Record.Recorded program request count} (resumed : IntegrationReplay.Resumed saved extra) :
    Observation.Record.Recorded program request (count + extra) where
  observation := resumed.observation
  trace := saved.trace ++ resumed.trace
  value_eq := (congrArg Basic.Execution.value
    (IntegrationReplay.resume_execution program request count extra saved)).trans resumed.value_eq
  trace_eq := by
    rw [resumed.trace_eq]
    exact (congrArg Basic.Execution.trace
      (IntegrationReplay.resume_execution program request count extra saved)).symm

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

/-- Every certified retained record equals the exact original deterministic recording.

The two records retain the same computation result and ordered transcript.
Their value and trace equations identify both data fields directly. -/
public theorem Recorded.eq_record {program : CachedProgram} {request : Request} {count : Nat}
    (saved : Observation.Record.Recorded program request count) : saved = Observation.Record.record program request
      count := by
  have observation_eq := Except.ok.inj (saved.value_eq.symm.trans (Observation.Record.record program request
    count).value_eq)
  have trace_eq := saved.trace_eq.trans (Observation.Record.record program request count).trace_eq.symm
  cases saved
  cases observation_eq
  cases trace_eq
  rfl

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

/-- The combined resumed record equals recording the original request for the full longer bit count.

The joined successful observation and trace identify the same
deterministic complete run at the extended bit count. -/
public theorem IntegrationReplay.Resumed.recorded_eq {program : CachedProgram} {request : Request} {count extra : Nat}
    {saved : Observation.Record.Recorded program request count} (resumed : IntegrationReplay.Resumed saved extra) :
    resumed.recorded = Observation.Record.record program request (count + extra) :=
  resumed.recorded.eq_record

/-- Resumption preserves the exact selected reading of the original saved observation.

The resumed record represents the same requested reading as the
original saved record, without making a new source selection. -/
public theorem IntegrationReplay.Resumed.selected_eq {program : CachedProgram} {request : Request} {count extra : Nat}
    {saved : Observation.Record.Recorded program request count} (resumed : IntegrationReplay.Resumed saved extra) :
    resumed.observation.selected = saved.observation.selected :=
  resumed.recorded.rep.1.trans saved.rep.1.symm

/-- Every new resumed reply is the exact original program stage at its retained query index.

The new transcript retains the exact saved-machine execution. Its
query membership identifies the corresponding original stage reply. -/
public theorem IntegrationReplay.Resumed.reply {program : CachedProgram} {request : Request} {count extra : Nat}
    {saved : Observation.Record.Recorded program request count} (resumed : IntegrationReplay.Resumed saved extra)
    (exchange : Basic.Exchange Nat CachedModel) (member : exchange ∈ resumed.trace) :
    exchange.reply = program.stage exchange.query := by
  rw [resumed.trace_eq] at member
  exact ((IntegrationReplay.resumeComputation (control program) saved.observation extra).answers_run
    program.stage exchange member).symm

/-- Replay the saved machine continuation against the exact supplied new transcript, preserving explicit failure types.

The same saved observation and additional bit count determine the
computation; transcript and numerical failures retain their original outcomes. -/
@[expose] public def IntegrationReplay.replayResume (control : Control) (saved : Observation) (extra :
  Nat) (trace : Trace) :
    Except Transcript.ReplayFailure Observation :=
  match (IntegrationReplay.resumeComputation control saved extra).replayExact trace with
  | .error error => .error (.transcript error)
  | .ok (.error error) => .error (.invalid error)
  | .ok (.ok observation) => .ok observation

/-- An empty transcript replays a zero-step continuation to the exact saved observation.

The empty transcript matches a zero-query continuation and returns
the same saved observation without replacing its machine. -/
public theorem IntegrationReplay.replayResume_zero (control : Control) (saved : Observation) :
    IntegrationReplay.replayResume control saved 0 [] = .ok saved := rfl

/-- A zero-step continuation rejects a nonempty transcript as trailing at its first query.

The first retained exchange is unconsumed by the zero-query
continuation, so its original query identifies the trailing failure. -/
public theorem IntegrationReplay.replayResume_zero_trailing (control : Control) (saved : Observation)
    (exchange : Basic.Exchange Nat CachedModel) (rest : Trace) :
    IntegrationReplay.replayResume control saved 0 (exchange :: rest) = .error (.transcript (.trailing exchange.query))
      := rfl

/-- The retained resumed transcript replays to the exact resumed observation.

The retained successful continuation value and exact new trace
supply the original source-free replay equation. -/
public theorem IntegrationReplay.Resumed.replay {program : CachedProgram} {request : Request} {count extra : Nat}
    {saved : Observation.Record.Recorded program request count} (resumed : IntegrationReplay.Resumed saved extra) :
    IntegrationReplay.replayResume (control program) saved.observation extra resumed.trace = .ok resumed.observation :=
      by
  rw [IntegrationReplay.replayResume, resumed.trace_eq, Computation.Query.Protocol.replayExact_run, resumed.value_eq]

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

end
