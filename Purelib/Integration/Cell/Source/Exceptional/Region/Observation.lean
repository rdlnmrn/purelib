module
public import Purelib.Integration.Cell.Source.Exceptional.Region.Builder
public import Purelib.Integration.Cell.Source.Observation
public import Purelib.Integration.Cell.Source.Observation.Continuation

/-!
# Observing effective-region source construction

The original selected finite regions, magnitude, regular modulus and finite
preparation are fixed inputs. Ordered interval-start replies construct the
original marked or regular ranges and the complete region-source result.
-/

public section

namespace Purelib.Integration.SourceFrontier.Exceptional.Region.Builder.Observation

open Purelib.Approximation
open Purelib.Approximation.Rational.Exceptional.Region (Modulus)
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.SourceFrontier.Observation

/-- The original marked-or-regular range for a retained region preparation. -/
@[expose] def range {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) :
    SourcePoint source → Purelib.Data.Rat.Interval :=
  readingRange prepared

/-- Assemble the region result from the actual returned source frontier. -/
@[expose] def assemble {source : Fraction.Rational → Fraction.Rational}
    {modulus : Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint
      source))
    (frontier : SourceFrontier.Observation.CertifiedFrontier prepared.partition (range prepared) prepared.rangeValid
      cached) :
    Result modulus := by
  have same : frontier.val = prepared.frontier := frontier.property.trans (prepared.frontierCached_eq cached)
  exact ⟨prepared, frontier.val, same, same.symm ▸ prepared.frontier_width_lt⟩

/-- The returned frontier assembles to the actual original cached region result. -/
theorem assemble_eq {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (frontier : SourceFrontier.Observation.CertifiedFrontier (Preparation.prepare modulus request).partition
      (range (Preparation.prepare modulus request)) (Preparation.prepare modulus request).rangeValid cached) :
    assemble (Preparation.prepare modulus request) cached frontier = buildCached modulus cached request := by
  cases frontier with
  | mk frontier equal =>
    cases equal
    rfl

/-- A complete region result certified as the original cache-aware producer output. -/
abbrev CertifiedResult {source : Fraction.Rational → Fraction.Rational} (modulus : Modulus source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :=
  {result : Result modulus // result = buildCached modulus cached request}

/-- Observe one retained region preparation and assemble its original certified result. -/
@[expose] def computationPrepared {source : Fraction.Rational → Fraction.Rational} (modulus : Modulus source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) (prepared : Preparation modulus)
    (same : prepared = Preparation.prepare modulus request) :
    Program (SourceFrontier.Observation.Entry prepared.partition) (SourcePoint source)
      (Except (SourceFrontier.Observation.InvalidTag prepared.partition) (CertifiedResult modulus cached request)) :=
  (SourceFrontier.Observation.computation prepared.partition (range prepared) prepared.rangeValid cached).map fun
    result =>
    result.map fun frontier => ⟨assemble prepared cached frontier, by
      cases same
      exact assemble_eq modulus cached request frontier⟩

/-- Observe the original region preparation and assemble its complete result from returned source points. -/
@[expose] def computation {source : Fraction.Rational → Fraction.Rational} (modulus : Modulus source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (SourceFrontier.Observation.Entry prepared.partition) (SourcePoint source)
      (Except (SourceFrontier.Observation.InvalidTag prepared.partition) (CertifiedResult modulus cached request)) :=
  computationPrepared modulus cached request (Preparation.prepare modulus request) rfl

/-- Original-source execution returns the complete actual cached region result. -/
theorem computation_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((computation modulus cached request).protocol.run (SourceFrontier.Observation.originalReply source
      prepared.partition)).value =
      .ok ⟨buildCached modulus cached request, rfl⟩ := by
  let prepared := Preparation.prepare modulus request
  change ((computation modulus cached request).protocol.run
    (SourceFrontier.Observation.originalReply source prepared.partition)).value = _
  unfold computation computationPrepared
  rw [Program.map_execution, Protocol.map_run_value, SourceFrontier.Observation.computation_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assemble_eq modulus cached request _

/-- Exact replay recovers the original region result without repeating source requests. -/
theorem computation_replay {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := computation modulus cached request
    program.protocol.replayExact (program.protocol.run (SourceFrontier.Observation.originalReply source
      prepared.partition)).trace =
      .ok (.ok ⟨buildCached modulus cached request, rfl⟩) := by
  let prepared := Preparation.prepare modulus request
  let program := computation modulus cached request
  change program.protocol.replayExact
    (program.protocol.run (SourceFrontier.Observation.originalReply source prepared.partition)).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Replies outside the executed region-source trace preserve the complete result and ordered trace. -/
theorem payload_erasure {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload)
    (outside : Payload → SourceFrontier.Observation.Entry (Preparation.prepare modulus request).partition →
      SourcePoint source) :
    let prepared := Preparation.prepare modulus request
    let program := computation modulus cached request
    program.protocol.run (Boundary.Trace.overlay
      (program.protocol.run (SourceFrontier.Observation.originalReply source prepared.partition)).trace (outside
        payload)) =
      program.protocol.run (SourceFrontier.Observation.originalReply source prepared.partition) :=
  (computation modulus cached request).protocol.annotation_erasure
    (SourceFrontier.Observation.originalReply source (Preparation.prepare modulus request).partition) payload outside

/-- Observe one public persistent request from its actual exceptional-source history. -/
@[expose] def historyComputation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Continuation.Query prepared.partition) (SourcePoint source)
      (Except (Continuation.Failure prepared.partition) (producer modulus).integrationProcess.State) := by
  if accurate : (integralBound state.1.cells).width < request.tolerance then
    exact .pure (.ok ⟨state.1, RefiningController.History.next state.2 (.reused request accurate)⟩)
  else
    let prepared := Preparation.prepare modulus request
    let cached := (producer modulus).retainedReadings state.2
    let effective := Producer.effectiveBank state.1 cached
    exact Continuation.historyRefiningPrepared prepared.partition (producer modulus) state request
      cached rfl effective rfl (computationPrepared modulus effective request prepared rfl)

/-- The shared-preparation history is the original composed history on every branch. -/
theorem historyComputation_eq {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :
    historyComputation modulus state request =
      Continuation.historyComputation (Preparation.prepare modulus request).partition (producer modulus) state request
        (computation modulus (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2))
          request) := by
  rw [Continuation.historyComputation_eq]
  unfold historyComputation
  by_cases accurate : (integralBound state.1.cells).width < request.tolerance
  · rw [dif_pos accurate]
    unfold Continuation.computation
    rw [dif_pos accurate]
    rfl
  · rw [dif_neg accurate]
    unfold Continuation.historyRefiningPrepared Continuation.computation computation
    rw [dif_neg accurate]
    rfl

/-- Original source execution returns the complete next public persistent history state. -/
theorem historyComputation_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((historyComputation modulus state request).protocol.run (Continuation.originalReplyAll prepared.partition)).value =
      .ok ((producer modulus).integrationProcess.request state request.tolerance request.positive) := by
  rw [historyComputation_eq]
  exact Continuation.historyComputation_original (Preparation.prepare modulus request).partition (producer modulus)
    state
    request
    (computation modulus (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2)) request)
    (computation_original modulus (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2))
      request)

/-- Exact replay recovers the complete public persistent state without repeating displayed source requests. -/
theorem historyComputation_replay {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := historyComputation modulus state request
    program.protocol.replayExact (program.protocol.run (Continuation.originalReplyAll prepared.partition)).trace =
      .ok (.ok ((producer modulus).integrationProcess.request state request.tolerance request.positive)) := by
  rw [historyComputation_eq]
  exact Continuation.historyComputation_replay (Preparation.prepare modulus request).partition (producer modulus) state
    request
    (computation modulus (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2)) request)
    (computation_original modulus (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2))
      request)

/-- Replies outside the actual public request trace preserve its complete state and ordered trace. -/
theorem historyComputation_payload_erasure {source : Fraction.Rational → Fraction.Rational}
    (modulus : Modulus source) (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload)
    (outside : Payload → Continuation.Query (Preparation.prepare modulus request).partition → SourcePoint source) :
    let prepared := Preparation.prepare modulus request
    let program := historyComputation modulus state request
    program.protocol.run (Boundary.Trace.overlay
      (program.protocol.run (Continuation.originalReplyAll prepared.partition)).trace (outside payload)) =
      program.protocol.run (Continuation.originalReplyAll prepared.partition) :=
  (historyComputation modulus state request).protocol.annotation_erasure
    (Continuation.originalReplyAll (Preparation.prepare modulus request).partition) payload outside

end Purelib.Integration.SourceFrontier.Exceptional.Region.Builder.Observation

end
