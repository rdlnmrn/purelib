module
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Computation.Query.Computation
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Integration.Program.Gaussian.CCL.Replay.Machine
public import Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Computation.Query.Basic
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Integration.Program.Gaussian.Cached.Basic

section
@[expose] public section

/-!
# Complete finite integration observations and source-free replay

A request records its selected rational enclosure and then every model read
used to produce the requested finite CCL prefix.  The retained numerical
machine contains no source callback.  Its projection to the existing
transducer is derived, including all chart changes and buffered bits.

The generic adapter inherits the supplied cached program's finite bounds and
coherence.  Generated polynomial, exponential and period clients discharge
those obligations in their own constructors.  No extra success, termination,
comparison or simulation premise is requested here.  Replay accepts only the
finite control, request, bit count and ordered model replies; it cannot call
the original evaluator.  Invalid invented logs do not establish global source
coherence, nor does this model boundary expose an opaque model's internals.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Representation

open Purelib.CCL.Progressive.IntegrationReplay

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- The retained observation has the original requested reading and represents the exact advanced refined-name machine.
-/
def ObservationRep (program :
  CachedProgram) (request : Request) (count : Nat)
    (observation : Integration.Program.Gaussian.CCL.Replay.Observation) : Prop :=
  observation.selected = requestedReading program request ∧
    MachineProjection.MachineRep program
      (Machine.Advance.advance (refinedName program request).machine count) observation.machine

open Purelib.Computation.Query in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Running the observation against its original program yields a successful exact represented observation. -/
theorem computation_rep (program :
  CachedProgram) (request : Request) (count : Nat) :
    ∃ observation, ((Observation.Basic.computation (control program) request count).run program.stage).value = .ok
      observation ∧
      ObservationRep program request count observation := by
  obtain ⟨machine, valueEqual, represented⟩ :=
    MachineProjection.initial_advance_rep program (selectedIndex (control program) request) count
  rw [Observation.Basic.computation, Computation.Query.Protocol.bind_run_value, requestReading,
    read_stage_value, Observation.Basic.continueObservation, Computation.Query.Protocol.map_run_value]
  change ∃ observation,
    Except.map (fun machine => (⟨requestedReading program request, machine⟩ :
      Integration.Program.Gaussian.CCL.Replay.Observation))
      ((Machine.advance (control program)
        (.initial (selectedIndex (control program) request)) count).run program.stage).value = .ok observation ∧ _
  rw [valueEqual]
  exact ⟨_, rfl, rfl, represented⟩

open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Every successful original-program observation result has the exact requested reading and machine representation. -/
theorem computation_ok_rep (program :
  CachedProgram) (request : Request) (count : Nat)
    (observation : Integration.Program.Gaussian.CCL.Replay.Observation)
    (success : ((Observation.Basic.computation (control program) request count).run program.stage).value = .ok
      observation) :
    ObservationRep program request count observation := by
  obtain ⟨expected, expectedEqual, represented⟩ := computation_rep program request count
  have equal : observation = expected := Except.ok.inj (success.symm.trans expectedEqual)
  exact equal.symm ▸ represented

open Purelib.Computation.Query in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- The original observation trace is its selected-stage exchange followed by the exact retained machine-advance trace.
-/
theorem computation_trace (program :
  CachedProgram) (request : Request) (count : Nat) :
    ((Observation.Basic.computation (control program) request count).run program.stage).trace =
      ⟨selectedIndex (control program) request, program.stage (selectedIndex (control program) request)⟩ ::
        ((Machine.advance (control program)
          (.initial (selectedIndex (control program) request)) count).run program.stage).trace := by
  rw [Observation.Basic.computation, Computation.Query.Protocol.bind_run_trace, requestReading, read_stage_value,
    Observation.Basic.continueObservation, Computation.Query.Protocol.map_run_trace, read_trace]
  rfl
end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Representation

end
