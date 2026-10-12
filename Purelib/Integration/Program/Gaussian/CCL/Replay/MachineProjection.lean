module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Process.Recipe.Request
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.List.Append
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Emission.Step
public import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Data.CCL.Transducer.Replay.Machine.Consume
import Purelib.Integration.Program.Gaussian.CCL.Replay.Controller
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Machine
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observe
import Purelib.Integration.Program.Gaussian.Query.Recipe
import Purelib.Computation.Query.Computation
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Representation
import Purelib.Integration.Program.Gaussian.CCL.Replay.StepProjection
import Purelib.Integration.Program.Gaussian.Query.CursorRepresentation

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.Computation.Query.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Transducer.Replay.Check
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Emission.Step
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Computation.Query.Iteration

/-!
# Total replay projection for arbitrary finite prefixes

The step simulation is iterated for the requested number of bits.  Generated
execution never requires a success assumption or an extra fuel parameter.
The relation includes pending bits and the complete numerical chart state,
so it also supports resuming any already-related finite machine.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection

open Purelib.Data.List

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Correspondence of exact machine modes with equality of the retained emitted prefix and pending bits.

The retained relation compares the original actual and replay modes
while separately preserving both ordered emitted and pending words. -/
@[expose] public def MachineRep (program : Basic.CachedProgram) (actual : Data.CCL.Transducer.Machine)
    (machine : Data.CCL.Transducer.Replay.Machine) : Prop :=
  Representation.ModeRep program actual.mode machine.mode ∧
    machine.emitted = actual.emitted ∧ machine.pending = actual.pending

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The source-index replay machine represents the exact original program process machine at that index.

The original source cursor represents the process at its supplied stage
index. Both machines start with the same empty emitted and pending words. -/
public theorem MachineRep.initial (program : Basic.CachedProgram) (index : Nat) :
    MachineProjection.MachineRep program (Data.CCL.Transducer.Machine.initial program.approximation.toProcess index)
      (Data.CCL.Transducer.Replay.Machine.initial index) :=
  ⟨Representation.ModeRep.initial _ _ (CursorRepresentation.CursorRep.source program index), rfl, rfl⟩

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Consuming a represented nonempty emission succeeds and preserves the exact actual machine representation.

The same certified nonempty emitted chunk determines the first bit,
remaining queue and next mode. Its original representation certifies the
replay machine without choosing another emission or process. -/
public theorem consume_rep (program : Basic.CachedProgram) (emitted : List Bool)
    (actual : Data.CCL.Transducer.Emission) (emission : Data.CCL.Transducer.Replay.Emission)
    (represented : Representation.EmissionRep program emission actual) :
    ∃ machine, Replay.Machine.Consume.consume emitted emission = .ok machine ∧
      MachineProjection.MachineRep program (Machine.Step.consumeEmission emitted actual).2 machine := by
  cases actual with
  | mk bits nonempty next =>
      cases emission with
      | mk otherBits otherNext =>
          obtain ⟨bitsEqual, nextRep⟩ := represented
          change otherBits = bits at bitsEqual
          cases bitsEqual
          cases bits with
          | nil => exact (nonempty rfl).elim
          | cons bit rest => exact ⟨_, rfl, nextRep, rfl, rfl⟩

section
open Purelib.CCL.Progressive
open Purelib.Computation.Query
open Purelib.Data.CCL.Transducer
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Integration.Program.Gaussian.Cached
/-- One retained replay bit step succeeds and represents the exact original process-backed machine step.

A pending bit preserves the exact represented mode and remaining queue.
An empty queue runs the retained controller emission once and transports
that same selected result through certified consumption. -/
public theorem nextBit_rep {program : Basic.CachedProgram} {actual : Data.CCL.Transducer.Machine} {machine :
  Data.CCL.Transducer.Replay.Machine}
    (represented : MachineProjection.MachineRep program actual machine) :
    ∃ next, ((Machine.nextBit (IntegrationReplay.control program) machine).run program.stage).value = .ok next ∧
      MachineProjection.MachineRep program (Machine.Step.nextBit actual).2 next := by
  cases actual with
  | mk actualMode actualEmitted actualPending =>
      cases machine with
      | mk mode emitted pending =>
          obtain ⟨modeRep, emittedEqual, pendingEqual⟩ := represented
          dsimp only at emittedEqual pendingEqual
          cases emittedEqual
          cases pendingEqual
          cases actualPending with
          | nil =>
              obtain ⟨emission, valueEqual, emissionRep⟩ := StepProjection.step_rep modeRep
              change ∃ next,
                (((Controller.step (IntegrationReplay.control program) mode).map
                  (fun result => result.bind (Replay.Machine.Consume.consume actualEmitted))).run program.stage).value =
                    .ok next ∧ _
              rw [Computation.Query.Protocol.map_run_value, valueEqual]
              exact MachineProjection.consume_rep program actualEmitted (Emission.Step.step actualMode) emission
                emissionRep
          | cons bit rest => exact ⟨_, rfl, modeRep, rfl, rfl⟩

/-- A finite retained replay advance succeeds and represents the exact original machine advance.

Induction on the requested finite count retains each successful next-bit
result as the following machine. The original actual machine and replay
procedure therefore share their complete selected state sequence. -/
public theorem advance_rep {program : Basic.CachedProgram} (count : Nat) :
    ∀ {actual : Data.CCL.Transducer.Machine} {machine : Data.CCL.Transducer.Replay.Machine},
      MachineProjection.MachineRep program actual machine →
      ∃ result, ((Machine.advance (IntegrationReplay.control program) machine count).run program.stage).value = .ok
        result ∧
        MachineProjection.MachineRep program (Machine.Advance.advance actual count) result := by
  induction count with
  | zero =>
      intro actual machine represented
      exact ⟨machine, rfl, represented⟩
  | succ count induction =>
      intro actual machine represented
      obtain ⟨next, nextEqual, nextRep⟩ := MachineProjection.nextBit_rep represented
      unfold Machine.advance
      rw [Computation.Query.Protocol.iterate, Computation.Query.Protocol.bind_run_value]
      change ∃ result,
        ((Computation.Query.Protocol.iterate _ count
          ((Machine.nextBit (IntegrationReplay.control program) machine).run program.stage).value).run
            program.stage).value =
            .ok result ∧ _
      rw [nextEqual]
      exact induction nextRep

end

open Purelib.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Advancing the original source-index replay machine represents the exact program machine at the same index and bit
count.

The original program process starts at the same supplied stage index.
Its finite actual advance and retained replay advance remain related
after every requested bit. -/
public theorem initial_advance_rep (program : Basic.CachedProgram) (index count : Nat) :
    ∃ result,
      ((Machine.advance (IntegrationReplay.control program) (Data.CCL.Transducer.Replay.Machine.initial index)
        count).run
        program.stage).value = .ok result ∧
      MachineProjection.MachineRep program
        (Machine.Advance.advance
          (Data.CCL.Transducer.Machine.initial program.approximation.toProcess index) count) result :=
  MachineProjection.advance_rep count (MachineProjection.MachineRep.initial program index)

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- The first replay bit step records exactly the source recipe's initial-budget refinement query and its oracle reply.

The first-bit computation retains the source recipe refinement query
and the oracle reply at exactly that source stage. No additional query
or reordering is introduced by the singleton advance. -/
public theorem initial_one_trace (control : IntegrationReplay.Control) (index : Nat)
    (oracle : Nat → Basic.CachedModel) :
    ((Machine.advance control (Data.CCL.Transducer.Replay.Machine.initial index) 1).run oracle).trace =
      [⟨Approximation.Gaussian.Process.Recipe.refine control .source index Emission.Initial.Budget.initialRadiusSq,
        oracle (Approximation.Gaussian.Process.Recipe.refine control .source index
            Emission.Initial.Budget.initialRadiusSq)⟩] :=
          by
  change (((Machine.nextBit control (Data.CCL.Transducer.Replay.Machine.initial index)).bind
    (fun result => Computation.Query.Protocol.pure result)).run oracle).trace = _
  rw [Computation.Query.Protocol.bind_run_trace]
  change ((Machine.nextBit control (Data.CCL.Transducer.Replay.Machine.initial index)).run oracle).trace ++ [] = _
  rw [Append.append_nil]
  change (((Controller.initialStep control ⟨.source, index⟩).map _).run oracle).trace = _
  rw [Computation.Query.Protocol.map_run_trace, Controller.initialStep,
    Computation.Query.Protocol.map_run_trace, Approximation.Gaussian.Process.Recipe.Cursor.observe,
    Computation.Query.Protocol.map_run_trace, Approximation.Gaussian.Process.Recipe.ball_trace]
  rfl

end Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection
