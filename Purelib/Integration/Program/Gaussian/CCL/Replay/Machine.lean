module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Iteration
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
public import Purelib.Data.CCL.Transducer.Replay.Machine.Consume
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Controller
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Computation.Query.Replay

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Machine

open Purelib.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Emit the next pending bit, or query one controller emission when the retained pending queue is empty.

The original mode and emitted prefix remain fixed until the checked controller result is consumed; failures remain
explicit. -/
def nextBit (control : IntegrationReplay.Control)
  (machine : Data.CCL.Transducer.Replay.Machine) : IntegrationReplay.QueryComputation (Except
    Data.CCL.Transducer.Replay.Failure
  Data.CCL.Transducer.Replay.Machine) :=
  match machine.pending with
  | bit :: rest => .pure (.ok ⟨machine.mode, machine.emitted ++ [bit], rest⟩)
  | [] => (Controller.step control machine.mode).map fun result => result.bind (Replay.Machine.Consume.consume
    machine.emitted)

open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Advance the retained replay machine by the requested finite number of bit steps, preserving any encountered failure.
-/
def advance (control : IntegrationReplay.Control)
  (machine : Data.CCL.Transducer.Replay.Machine) (count : Nat) :
    IntegrationReplay.QueryComputation (Except Data.CCL.Transducer.Replay.Failure Data.CCL.Transducer.Replay.Machine) :=
  Computation.Query.Protocol.iterate
    (fun result => match result with
      | .error error => .pure (.error error)
      | .ok current => nextBit control current)
    count (.ok machine)

open Purelib.CCL.Progressive
open Purelib.Computation.Query
open Purelib.Data.CCL.Transducer
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Integration.Program.Gaussian.Cached
/-- Replaying the exact recorded query trace recovers the original finite advance result. -/
theorem advance_replay (control :
  IntegrationReplay.Control) (machine : Data.CCL.Transducer.Replay.Machine) (count : Nat)
    (oracle : Nat → Basic.CachedModel) :
    (advance control machine count).replayExact ((advance control machine count).run oracle).trace =
      .ok ((advance control machine count).run oracle).value :=
  Computation.Query.Protocol.replayExact_run _ _

/-- An oracle agreeing with every retained reply produces the same finite advance result and query trace. -/
theorem advance_run_of_answers (control :
  IntegrationReplay.Control) (machine : Data.CCL.Transducer.Replay.Machine) (count : Nat)
    (first second : Nat → Basic.CachedModel)
    (agrees : Basic.Answers second ((advance control machine count).run first).trace) :
    (advance control machine count).run second = (advance control machine count).run first :=
  Computation.Query.Protocol.run_of_answers _ first second agrees

end Purelib.Integration.Program.Gaussian.CCL.Replay.Machine

end

section

@[expose] public section

/-!
# Resuming certified finite integration observations

Resume consumes the retained numerical machine, including its pending bits;
it does not select the enclosure again or restart prefix production.  The
new receipt stores only newly consumed replies.  Joining it to the saved
receipt gives exactly the uninterrupted observation and ordered trace.

The saved receipt is produced by `record`, not a caller-supplied simulation
or success hypothesis.  Any finite extra bit count is supported.  Raw replay
still accepts only finite control, the saved observation and the new replies,
and reports malformed transcripts or invalid numerical replies explicitly.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Machine.ReplayController

open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- A successful initial advance followed by extra steps equals advancing by their sum with the two exact query traces
appended.

The supplied success equation retains the actual first resulting machine.
Iteration then concatenates its saved transcript with the exact new replies. -/
theorem advance_run_add_of_ok (control :
  IntegrationReplay.Control)
    (machine next : Data.CCL.Transducer.Replay.Machine) (first extra : Nat)
    (oracle : Nat → Basic.CachedModel)
    (success : ((Machine.advance control machine first).run oracle).value = .ok next) :
    (Machine.advance control machine (first + extra)).run oracle =
      let after := (Machine.advance control next extra).run oracle
      ⟨after.value, ((Machine.advance control machine first).run oracle).trace ++ after.trace⟩ := by
  unfold Machine.advance at success ⊢
  rw [Computation.Query.Protocol.iterate_run_add]
  dsimp only
  rewrite [success]
  exact Eq.refl _

end Purelib.Integration.Program.Gaussian.CCL.Replay.Machine.ReplayController

end
