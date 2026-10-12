module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.List.GetD
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Computation.Query.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Representation
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.List.Basic
import Purelib.Computation.Query.Computation
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Name.Basic

section
public section

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

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

open Purelib.CCL.Progressive.IntegrationReplay

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.Integration.Program.Gaussian.CCL.Replay in
set_option genInjectivity false in
/-- A retained successful observation and exact query transcript for one original program, request and bit count.

The value and trace equations bind both retained outputs to the same original observation computation. -/
structure Recorded (program : CachedProgram) (request : Request) (count : Nat) where
  /-- The exact retained successful observation. -/ observation : Observation
  /-- The retained ordered query-and-reply transcript. -/ trace : Trace
  /-- The original computation returns this exact successful observation. -/ value_eq : ((Observation.Basic.computation
    (control program) request count).run program.stage).value = .ok observation
  /-- The retained transcript equals the exact original computation trace. -/ trace_eq : trace =
    ((Observation.Basic.computation (control program) request count).run program.stage).trace

constructive_injectivity Recorded

section
open Purelib.Integration.Program.Gaussian.CCL.Replay
/-- Run the exact original observation computation once and retain its successful observation and transcript.

The representation theorem rules out an error for this program without replacing the actual executed result. -/
@[expose] def record (program : CachedProgram) (request : Request) (count : Nat) : Observation.Record.Recorded program
  request count :=
  let execution := (Observation.Basic.computation (control program) request count).run program.stage
  match result : execution.value with
  | .ok observation =>
      { observation := observation, trace := execution.trace, value_eq := result, trace_eq := rfl }
  | .error error => by
      have impossible : False := by
        obtain ⟨observation, successful, _⟩ := Observation.Representation.computation_rep program request count
        have unequal : Except.error error = Except.ok observation := result.symm.trans successful
        nomatch unequal
      nomatch impossible

/-- The recorded observation has the exact original reading and process-backed machine representation. -/
theorem Recorded.rep {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Observation.Record.Recorded program request count) :
    Observation.Representation.ObservationRep program request count recorded.observation :=
  Observation.Representation.computation_ok_rep program request count recorded.observation recorded.value_eq

/-- Every successful observation retains its initial selected-stage exchange.

The query protocol records the requested model before emitting any bits, so
this claim also covers an observation requesting an empty prefix. -/
theorem Recorded.trace_nonempty {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Recorded program request count) : recorded.trace ≠ [] := by
  rw [recorded.trace_eq, Observation.Representation.computation_trace]
  intro impossible
  cases impossible

/-- Read the actual initial exchange from the retained observation transcript.

The original successful execution certifies that this exchange exists. The
projection reads the retained list head and never invokes the stage source. -/
@[expose] def Recorded.selectedExchange {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Recorded program request count) : Purelib.Computation.Query.Basic.Exchange Nat CachedModel :=
  recorded.trace.head recorded.trace_nonempty

/-- The initial retained exchange has the original selected index and stage reply. -/
theorem Recorded.selectedExchange_eq {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Recorded program request count) :
    recorded.selectedExchange =
      ⟨selectedIndex (control program) request, program.stage (selectedIndex (control program) request)⟩ := by
  have first : ∀ (values : Trace) (nonempty : values ≠ []) (tail : Trace),
      values = ⟨selectedIndex (control program) request,
        program.stage (selectedIndex (control program) request)⟩ :: tail →
      values.head nonempty = ⟨selectedIndex (control program) request,
        program.stage (selectedIndex (control program) request)⟩ := by
    intro values nonempty tail same
    cases same
    rfl
  exact first recorded.trace recorded.trace_nonempty _
    (recorded.trace_eq.trans (Observation.Representation.computation_trace program request count))

/-- The selected observation retains the original prepared request's squared radius. -/
theorem Recorded.selected_radius {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Recorded program request count) :
    recorded.observation.selected.ball.radiusSq = (program.prepare request).radiusSq :=
  congrArg (fun selected => selected.ball.radiusSq) recorded.rep.1

/-- Recover the typed prepared request from an observation's retained initial reply.

The index and complete cache come from the actual transcript, and the squared
radius comes from the retained selected reading. The original program supplies
accuracy and ownership certificates without another executable stage query. -/
@[expose] def Recorded.preparedRequest {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Recorded program request count) :
    Purelib.Integration.CertifiedProgram.Program.Prepared program request :=
  let exchange := recorded.selectedExchange
  have exchange_eq : exchange =
      ⟨selectedIndex (control program) request, program.stage (selectedIndex (control program) request)⟩ :=
    recorded.selectedExchange_eq
  { index := exchange.query
    index_eq := by rw [exchange_eq]; rfl
    index_ge := by
      rw [exchange_eq]
      exact (program.prepare request).index_ge
    cache := exchange.reply
    cache_eq := by rw [exchange_eq]
    radiusSq := recorded.observation.selected.ball.radiusSq
    radiusSq_eq := by
      rw [recorded.selected_radius, exchange_eq]
      exact (program.prepare request).radiusSq_eq
    radiusSq_nonnegative := by
      rw [recorded.selected_radius]
      exact (program.prepare request).radiusSq_nonnegative
    radiusSq_accurate := by
      rw [recorded.selected_radius]
      exact (program.prepare request).radiusSq_accurate
    allowance_accurate := by
      rw [exchange_eq]
      exact (program.prepare request).allowance_accurate
    center_bounded := by
      rw [exchange_eq]
      exact (program.prepare request).center_bounded }

/-- Reading the recovered prepared cache gives the exact retained selected observation. -/
theorem Recorded.preparedRequest_reading {program : CachedProgram} {request : Request} {count : Nat}
    (recorded : Recorded program request count) :
    reading (control program) recorded.preparedRequest.index recorded.preparedRequest.cache =
      recorded.observation.selected := by
  change reading (control program) recorded.selectedExchange.query recorded.selectedExchange.reply = _
  rw [recorded.selectedExchange_eq, recorded.rep.1]
  rfl

/-- The recorded observation retains the exact original requested reading. -/
theorem recorded_selected (program : CachedProgram) (request : Request) (count : Nat) :
    (Observation.Record.record program request count).observation.selected = requestedReading program request :=
  (Observation.Record.record program request count).rep.1

end

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- The recorded word equals the exact advanced refined-name machine's emitted prefix. -/
theorem recorded_prefix (program : CachedProgram) (request : Request) (count : Nat) :
    (Observation.Record.record program request count).observation.word =
      (Machine.Advance.advance (refinedName program request).machine count).emitted :=
  (Observation.Record.record program request count).rep.2.2.1

section
open Purelib.Integration.Program.Gaussian.CCL.Replay
/-- The retained selected ball radius is strictly below the original target. -/
theorem recorded_accurate (program : CachedProgram) (request : Request) (count : Nat) :
    (Observation.Record.record program request count).observation.selected.ball.radiusSq < request.target := by
  rw [Observation.Record.recorded_selected]
  exact requestedReading_accurate program request

/-- The retained selected model allowance is strictly below the original target. -/
theorem recorded_allowance (program : CachedProgram) (request : Request) (count : Nat) :
    (Observation.Record.record program request count).observation.selected.allowance < request.target := by
  rw [Observation.Record.recorded_selected]
  exact requestedReading_allowance program request

/-- The recorded selected ball contains every later original program sample. -/
theorem recorded_contains_later (program : CachedProgram) (request : Request) (count : Nat)
    {later : Nat} (order : selectedIndex (control program) request ≤ later) :
    (Observation.Record.record program request count).observation.selected.ball.Contains (program.stage later).sample :=
      by
  rw [Observation.Record.recorded_selected]
  exact requestedReading_contains_later program request order

/-- The recorded word has exactly the originally requested bit count. -/
theorem recorded_length (program : CachedProgram) (request : Request) (count : Nat) :
    (Observation.Record.record program request count).observation.word.length = count := by
  rw [Observation.Record.recorded_prefix]
  exact ((refinedName program request).productive count).2

/-- The first retained transcript reply contains the exact selected original stage model. -/
theorem recorded_model (program : CachedProgram) (request : Request) (count : Nat) :
    (Purelib.Data.List.getElem? (Observation.Record.record program request count).trace 0).map (fun exchange =>
      exchange.reply.model) =
      some (program.stage (selectedIndex (control program) request)).model := by
  rw [(Observation.Record.record program request count).trace_eq, Observation.Representation.computation_trace]
  rfl

end

open Purelib.Computation.Query in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Every retained transcript reply is the exact original program stage at its recorded query index. -/
theorem recorded_reply (program : CachedProgram) (request : Request) (count : Nat)
    (exchange : Basic.Exchange Nat CachedModel)
    (member : exchange ∈ (Observation.Record.record program request count).trace) :
    exchange.reply = program.stage exchange.query := by
  rw [(Observation.Record.record program request count).trace_eq] at member
  exact ((Observation.Basic.computation (control program) request count).answers_run program.stage exchange member).symm

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- The recorded word comes from an actual machine retaining exact semantics for the original refined name. -/
theorem recorded_exactCursor (program : CachedProgram) (request : Request) (count : Nat) :
    ∃ actual : Data.CCL.Transducer.Machine,
      actual.emitted = (Observation.Record.record program request count).observation.word ∧
      Machine.Semantics.Basic.ExactCursor
        (refinedName program request).process (refinedName program request).state actual :=
  ⟨Machine.Advance.advance (refinedName program request).machine count,
    (Observation.Record.recorded_prefix program request count).symm,
    Name.CCL.Semantics.Named.advance_exact (refinedName program request) count⟩

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Requesting additional bits preserves the original recorded word as a prefix. -/
theorem recorded_extends (program : CachedProgram) (request : Request) (count extra : Nat) :
    (Observation.Record.record program request count).observation.word.IsPrefix
      (Observation.Record.record program request (count + extra)).observation.word := by
  rw [Observation.Record.recorded_prefix, Observation.Record.recorded_prefix, ← Machine.Advance.advance_add]
  exact Machine.Advance.advance_extends _ extra
end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

end
