module

public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Receipt
public import Purelib.CCL.Progressive.IntegrationPrograms
public import Purelib.Computation.Query.Program.Certified.Cache

/-!
# Original polynomial runner and ordered path observations

The original policy compiler supplies indexed receipts retaining the actual
compiled partition. The same receipt supplies the model to the original
integration continuation and the selected compiled sample to the ordered
real and imaginary path observations.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner

open Purelib.Approximation
open Purelib.CCL.Progressive.IntegrationPrograms
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Integration.Program.Gaussian.CCL
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
open Purelib.Integration.Polynomial.Gaussian.Partition
open Purelib.Integration.SourceFrontier.Continuous

variable {source : Source.PolynomialPath} {policy : PartitionPolicy source}

set_option genInjectivity false in
/-- An actual compiled partition and its original policy-selected stage index. -/
structure StageReceipt (retained : Retained source policy) where
  /-- The original reported stage. -/ index : Nat
  /-- The actual compiled partition supplied to the original model continuation. -/ compiled :
    Compiled.CompiledPartition source
  /-- The compilation belongs to this retained policy at the reported index. -/ compiled_eq :
    compiled = retained.compiled index

/-- Construct the original compiled partition once at the requested index. -/
@[expose] def stageReply (retained : Retained source policy) (index : Nat) : StageReceipt retained :=
  ⟨index, retained.compiled index, rfl⟩

/-- The original cached-model program with its actual source-indexed partition receipts. -/
@[expose] def receiptSource (retained : Retained source policy) :
    Program.Certified.Source CachedModel (StageReceipt retained) where
  stage := retained.program.stage
  index := StageReceipt.index
  model := fun receipt => CachedModel.ofPartition receipt.compiled
  model_eq := fun receipt =>
    (congrArg CachedModel.ofPartition receipt.compiled_eq).trans (retained.stage_eq receipt.index).symm

set_option genInjectivity false in
/-- The original polynomial program request and saved ordered path states. -/
structure Input (source : Source.PolynomialPath) (policy : PartitionPolicy source) where
  /-- The original compiler and its shared stage-program closure. -/ retained : Retained source policy
  /-- The original positive integration request. -/ request : CertifiedProgram.Request
  /-- The number of requested original output bits. -/ count : Nat
  /-- The original saved real-coordinate path state. -/ real : RealState source
  /-- The original saved imaginary-coordinate path state. -/ imaginary : ImaginaryState source
  /-- The real-coordinate source request. -/ realRequest : AccuracyRequest
  /-- The imaginary-coordinate source request. -/ imaginaryRequest : AccuracyRequest
  /-- Previously returned compiled receipts from this exact retained program. -/ bank : List (StageReceipt retained)

variable (input : Input source policy)

/-- One original model query or one subsequent ordered path-source query. -/
abbrev Question := Sum Nat (Query source input.realRequest input.imaginaryRequest)

/-- One original compiled-stage receipt or an owner-specific ordered path reply. -/
abbrev Reply := Sum (StageReceipt input.retained) (Observation.Reply source)

/-- The original integration program with actual retained compiled-stage receipts. -/
abbrev ReceiptExecution := Replay.Observation.Receipt.Execution input.retained.program
  (receiptSource input.retained) input.request input.count

/-- The original successful integration record and complete model transcript. -/
abbrev Recorded := Record.Recorded input.retained.program input.request input.count

/-- The complete returned model occurrence trace and its actual retained bank. -/
abbrev Completed := Program.Certified.Cache.Completed (receiptSource input.retained) input.bank
  (Expansion.program (control input.retained.program) input.request input.count)

/-- Recover the original runner record from the actual completed receipt execution. -/
@[expose] def completedRecord (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) : Recorded input :=
  Replay.Observation.Receipt.record input.retained.program (receiptSource input.retained) rfl
    input.request input.count completed.execution observation success

/-- Recover the actual selected compiled partition from the completed receipt execution. -/
@[expose] def completedSelection (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) : StageReceipt input.retained :=
  Replay.Observation.Receipt.selected input.retained.program (receiptSource input.retained) rfl
    input.request input.count completed.execution observation success

/-- The completed selection belongs to the original requested integration stage. -/
theorem completedSelection_index (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) :
    (completedSelection input completed observation success).index =
      selectedIndex (control input.retained.program) input.request :=
  Replay.Observation.Receipt.selected_index input.retained.program (receiptSource input.retained) rfl
    input.request input.count completed.execution observation success

/-- The completed selection's model is the original record's actual selected model. -/
theorem completedSelection_model (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) :
    CachedModel.ofPartition (completedSelection input completed observation success).compiled =
      (completedRecord input completed observation success).selectedExchange.reply :=
  Replay.Observation.Receipt.selected_model input.retained.program (receiptSource input.retained) rfl
    input.request input.count completed.execution observation success

set_option genInjectivity false in
/-- The first wrong operation, indexed-stage receipt, original runner error or path failure. -/
inductive Failure where
  /-- The original model request received a wrong operation or index, retaining its bank. -/ | modelFailure
      (failure : Program.Certified.Cache.Failure (receiptSource input.retained))
  /-- The original runner failed after returning the complete receipt execution and bank. -/ | runner
      (completed : Completed input) (failure : Purelib.Data.CCL.Transducer.Replay.Failure)
      (value_eq : completed.execution.val.value = .error failure)
  /-- A path query received a model reply after the retained original runner succeeded. -/ | pathOperation
      (completed : Completed input) (observation : Replay.Observation)
      (success : completed.execution.val.value = .ok observation)
      (question : Query source input.realRequest input.imaginaryRequest)
  /-- The original ordered path request returned its typed failure after the retained runner. -/ | path
      (completed : Completed input) (observation : Replay.Observation)
      (success : completed.execution.val.value = .ok observation)
      (failure : Observation.Failure source input.realRequest input.imaginaryRequest)

set_option genInjectivity false in
/-- The returned runner record, its actual selected partition receipt and both returned path states. -/
structure Result where
  /-- The actual original model transcript and successful observation. -/ recorded : Recorded input
  /-- The selected compiled partition taken from the actual first receipt. -/ selected : StageReceipt input.retained
  /-- The selected receipt belongs to the runner's actual selected stage. -/ selected_index :
    selected.index = selectedIndex (control input.retained.program) input.request
  /-- The receipt's compiled model is the model returned in the runner transcript. -/ selected_model :
    CachedModel.ofPartition selected.compiled = recorded.selectedExchange.reply
  /-- The actual updated bank of compiled-stage receipts. -/ bank : List (StageReceipt input.retained)
  /-- The original caller's bank remains the exact tail. -/ bank_retained : ∃ added, bank = added ++ input.bank
  /-- The actual returned real-coordinate path state. -/ real : RealState source
  /-- The actual returned imaginary-coordinate path state. -/ imaginary : ImaginaryState source

/-- Continue the same original runner from its actual returned bank and ordered path states. -/
@[expose] def Result.continuation {input : Input source policy} (result : Result input)
    (request : CertifiedProgram.Request) (count : Nat)
    (realRequest imaginaryRequest : AccuracyRequest) : Input source policy :=
  ⟨input.retained, request, count, result.real, result.imaginary, realRequest, imaginaryRequest, result.bank⟩

/-- The continued request uses the exact bank returned by its original execution. -/
theorem Result.continuation_bank (result : Result input) (request : CertifiedProgram.Request) (count : Nat)
    (realRequest imaginaryRequest : AccuracyRequest) :
    (result.continuation request count realRequest imaginaryRequest).bank = result.bank := rfl

/-- Answer each original model or ordered source query from its own retained owner. -/
@[expose] def originalReply : Question input → Reply input
  | .inl index => .inl (stageReply input.retained index)
  | .inr question => .inr (pathReply source input.realRequest input.imaginaryRequest question)

/-- Forward an original model query as an optional compiled-stage receipt. -/
private def modelHandler (index : Nat) :
    Program (Question input) (Reply input) (Except Empty (Option (StageReceipt input.retained))) :=
  .request (.inl index) fun reply => match reply with
    | .inl receipt => .pure (.ok (some receipt))
    | .inr _ => .pure (.ok none)

/-- Run original model requests, reusing the same-owner compiled receipt bank. -/
def modelProgram : Program (Question input) (Reply input) (Except Empty
    (Basic.Execution Nat (Option (StageReceipt input.retained))
      (Except (Program.Certified.Cache.Failure (receiptSource input.retained))
        (Program.Certified.Cache.Completed (receiptSource input.retained) input.bank
          (Expansion.program (control input.retained.program) input.request input.count))))) :=
  (Program.Certified.Cache.computation (receiptSource input.retained) input.bank
    (Expansion.program (control input.retained.program) input.request input.count)).substituteChecked
      (modelHandler input)

/-- Forward an original path question, retaining the already returned runner record on failure. -/
private def pathHandler (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation)
    (question : Query source input.realRequest input.imaginaryRequest) :
    Program (Question input) (Reply input) (Except (Failure input) (Observation.Reply source)) :=
  .request (.inr question) fun reply => match reply with
    | .inl _ => .pure (.error (.pathOperation completed observation success question))
    | .inr point => .pure (.ok point)

/-- Run both original ordered path requests through their actual returned source replies. -/
def pathProgram (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) :=
  (Observation.computation source input.real input.imaginary input.realRequest input.imaginaryRequest).substituteChecked
    (pathHandler input completed observation success)

/-- Run original model acquisition and the selected compiled partition's ordered path observation.

The selected partition comes from the actual first model receipt. Its model
drives the original integration continuation, and both returned path states
are kept with that same compiled source owner. Typed failures stop the
combined program before any later requests. -/
@[expose] def computation : Program (Question input) (Reply input) (Except (Failure input) (Result input)) :=
  (modelProgram input).bind fun modelResult =>
    match modelResult with
    | .error impossible => nomatch impossible
    | .ok modelExecution =>
        match modelExecution.value with
        | .error invalid => .pure (.error (.modelFailure invalid))
        | .ok completed =>
            match success : completed.execution.val.value with
            | .error failure => .pure (.error (.runner completed failure success))
            | .ok observation =>
                let original := completedRecord input completed observation success
                let selected := completedSelection input completed observation success
                let selected_index := completedSelection_index input completed observation success
                let selected_model := completedSelection_model input completed observation success
                (pathProgram input completed observation success).map fun pathResult =>
                  match pathResult with
                  | .error failure => .error failure
                  | .ok pathExecution =>
                      match pathExecution.value with
                      | .error failure => .error (.path completed observation success failure)
                      | .ok (real, imaginary) =>
                          .ok ⟨original, selected, selected_index, selected_model, completed.bank,
                            completed.retained, real, imaginary⟩

/-- The original selected integration reading is the actual returned partition's cached sample. -/
theorem Result.selected_sample (result : Result input) :
    result.recorded.observation.selected.sample = result.selected.compiled.sample := by
  have reading := congrArg (fun value : Reading => value.sample) result.recorded.preparedRequest_reading
  change result.recorded.selectedExchange.reply.sample = result.recorded.observation.selected.sample at reading
  have model := congrArg (fun cache : CachedModel => cache.sample) result.selected_model
  change result.selected.compiled.sample = result.recorded.selectedExchange.reply.sample at model
  exact reading.symm.trans model.symm

/-- The actual selected runner sample is bounded by the two returned path midpoint widths. -/
theorem Result.sample_midpoint_normSq_le (result : Result input) :
    Norm.Basic.normSq (result.recorded.observation.selected.sample - midpoint source result.real result.imaginary) ≤
      (((boundProcess source).bound result.real).width * (1 / 2)) ^ 2 +
      (((imaginaryBoundProcess source).bound result.imaginary).width * (1 / 2)) ^ 2 := by
  rw [result.selected_sample, result.selected.compiled.sample_eq]
  exact Cells.Continuous.sample_midpoint_normSq_le result.selected.compiled.cells result.real result.imaginary



/-! Compare two returned polynomial runners with the same original source. -/

/-- Original runner samples agree exactly for independently selected partitions of the same source. -/
theorem Result.selected_samples_eq {leftPolicy rightPolicy : PartitionPolicy source}
    {leftInput : Input source leftPolicy} {rightInput : Input source rightPolicy}
    (left : Result leftInput) (right : Result rightInput) :
    left.recorded.observation.selected.sample = right.recorded.observation.selected.sample :=
  left.selected_sample.trans (left.selected.compiled.sample_source.trans
    (right.selected.compiled.sample_source.symm.trans right.selected_sample.symm))

/-- Independently returned path midpoints satisfy the actual two-coordinate width budget.

The inputs may retain different partition policies and path histories. Both
compiled partitions come from their respective actual runner receipts, and
the four widths come from their actual returned coordinate states. -/
theorem Result.midpoints_normSq_le {leftPolicy rightPolicy : PartitionPolicy source}
    {leftInput : Input source leftPolicy} {rightInput : Input source rightPolicy}
    (left : Result leftInput) (right : Result rightInput) :
    Norm.Basic.normSq (midpoint source left.real left.imaginary - midpoint source right.real right.imaginary) ≤
      (((boundProcess source).bound left.real).width + ((boundProcess source).bound right.real).width) ^ 2 +
      (((imaginaryBoundProcess source).bound left.imaginary).width +
        ((imaginaryBoundProcess source).bound right.imaginary).width) ^ 2 :=
  Cells.Continuous.midpoints_normSq_le left.selected.compiled.cells right.selected.compiled.cells
    left.real right.real left.imaginary right.imaginary

/-- Original model replies reproduce the complete authenticated receipt execution. -/
private theorem modelProgram_original :
    ((modelProgram input).protocol.run (originalReply input)).value =
      .ok ((Program.Certified.Cache.computation (receiptSource input.retained) input.bank
        (Expansion.program (control input.retained.program) input.request input.count)).protocol.run
          (fun index => some (stageReply input.retained index))) := by
  unfold modelProgram
  apply Program.substituteChecked_value
  intro index
  rfl

/-- Original source replies reproduce the complete ordered path execution. -/
private theorem pathProgram_original (completed : Completed input) (observation : Replay.Observation)
    (success : completed.execution.val.value = .ok observation) :
    ((pathProgram input completed observation success).protocol.run (originalReply input)).value =
      .ok ((Observation.computation source input.real input.imaginary input.realRequest
        input.imaginaryRequest).protocol.run (pathReply source input.realRequest input.imaginaryRequest)) := by
  unfold pathProgram
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Records of the same original program, request and output count are identical. -/
private theorem recorded_unique (first second : Recorded input) : first = second := by
  have observation_eq : first.observation = second.observation :=
    Except.ok.inj (first.value_eq.symm.trans second.value_eq)
  have trace_eq : first.trace = second.trace := first.trace_eq.trans second.trace_eq.symm
  cases first with
  | mk firstObservation firstTrace firstValue firstTraceEq =>
    cases second with
    | mk secondObservation secondTrace secondValue secondTraceEq =>
      cases observation_eq
      cases trace_eq
      rfl

/-- Original replies return the original runner record and both original ordered path continuations. -/
theorem computation_original :
    ∃ result : Result input,
      ((computation input).protocol.run (originalReply input)).value = .ok result ∧
      result.recorded = Record.record input.retained.program input.request input.count ∧
      result.real = (boundProcess source).request input.real input.realRequest.tolerance input.realRequest.positive ∧
      result.imaginary = (imaginaryBoundProcess source).request input.imaginary
        input.imaginaryRequest.tolerance input.imaginaryRequest.positive := by
  let original := Record.record input.retained.program input.request input.count
  let originalProgram := Expansion.program (control input.retained.program) input.request input.count
  have runnerValue : (originalProgram.protocol.run input.retained.program.stage).value =
      .ok original.observation := by
    rw [Expansion.program_execution]
    exact original.value_eq
  obtain ⟨completed, returned⟩ := Program.Certified.Cache.computation_original
    (receiptSource input.retained) (stageReply input.retained) (fun _ => rfl) originalProgram input.bank
  have projectedValue : completed.execution.val.value = .ok original.observation :=
    (congrArg Basic.Execution.value completed.execution.property.1).trans runnerValue
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, modelProgram_original]
  dsimp only
  rw [returned]
  dsimp only
  split
  next failure failed =>
    have impossible : Except.error failure = Except.ok original.observation := failed.symm.trans projectedValue
    cases impossible
  next observation success =>
    rw [Program.map_execution, Protocol.map_run_value, pathProgram_original]
    dsimp only
    rw [Observation.computation_original]
    refine ⟨_, rfl, ?_, rfl, rfl⟩
    exact recorded_unique input _ original

/-- Exact replay preserves the complete successful result or first typed failure. -/
theorem computation_replay (oracle : Question input → Reply input) :
    (computation input).protocol.replayExact ((computation input).protocol.run oracle).trace =
      .ok ((computation input).protocol.run oracle).value :=
  (computation input).protocol.replayExact_run oracle

/-- Changing replies outside the actual model-and-path trace preserves the complete execution. -/
theorem payload_erasure {Payload : Type} (oracle : Question input → Reply input) (payload : Payload)
    (outside : Payload → Question input → Reply input) :
    (computation input).protocol.run (Boundary.Trace.overlay
      ((computation input).protocol.run oracle).trace (outside payload)) = (computation input).protocol.run oracle :=
  (computation input).protocol.annotation_erasure oracle payload outside

end Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous.Observation.Runner

end
