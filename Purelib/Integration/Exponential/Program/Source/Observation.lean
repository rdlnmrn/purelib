module
public import Purelib.Integration.Exponential.Program.Source
public import Purelib.Integration.Cell.Source.Continuous.Observation
public import Purelib.Integration.Cell.Source.Continuous.Observation.Continuation

/-!
# Observing original exponential stage-source construction

The original policy, schedule, stage index and request select the same cached
Taylor model and source preparation as the public stage-source builder. The
displayed rational source replies are consumed directly by that original
result; the policy and finite stage preparation are fixed inputs.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Computation.Query
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.SourceFrontier
open Purelib.Integration.SourceFrontier.Continuous
open Purelib.Integration.SourceFrontier.Continuous.Observation

/-- The original policy-selected finite Taylor source preparation for a stage request. -/
@[expose] def preparation (policy : Geometry.Policy) (schedule : PositiveStride) (index : Nat)
    (request : AccuracyRequest) :
    Preparation (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) :=
  Preparation.prepare (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) request

/-- Assemble a stage-source result using the supplied original program, cached stage and returned source result.

The supplied stage is the actual retained cache from the original program.
Its identity proof connects it to that program's requested index; source
cells come directly from the returned exact source construction. -/
@[expose] def assembleAt (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (original : Cached.Basic.CachedProgram) (original_eq : original = Program.program policy schedule extraDepth)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = original.stage index)
    (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult
      (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request) :
    Result policy schedule extraDepth index request := by
  have source_eq : fresh.val = (Source.build policy schedule extraDepth index request).sourceResult := by
    exact fresh.property.trans (SourceFrontier.Continuous.buildCached_eq _ [] request)
  have request_eq : fresh.val.preparation.request = request := by
    rw [source_eq]
    rfl
  have inside : (integralBound fresh.val.frontier.cells).Contains stage.sample.re := by
    rw [source_eq, stage_eq, original_eq]
    exact (Source.build policy schedule extraDepth index request).sample_inside
  exact ⟨original, original_eq, stage, stage_eq, fresh.val, request_eq, inside⟩

/-- Assemble a stage-source result using the supplied retained program's requested stage. -/
@[expose] def assembleWith (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (original : Cached.Basic.CachedProgram) (original_eq : original = Program.program policy schedule extraDepth)
    (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult
      (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request) :
    Result policy schedule extraDepth index request :=
  assembleAt policy schedule extraDepth index original original_eq (original.stage index) rfl request fresh

/-- Assemble the original cached exponential stage from the returned exact source result. -/
@[expose] def assemble (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult
      (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request) :
    Result policy schedule extraDepth index request :=
  assembleWith policy schedule extraDepth index (Program.program policy schedule extraDepth) rfl request fresh

/-- The supplied program, its cached stage and returned source result assemble to the original stage result. -/
theorem assembleAt_eq_build (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (original : Cached.Basic.CachedProgram) (original_eq : original = Program.program policy schedule extraDepth)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = original.stage index)
    (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult
      (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request) :
    assembleAt policy schedule extraDepth index original original_eq stage stage_eq request fresh =
      Source.build policy schedule extraDepth index request := by
  refine Result.ext _ _ ?_ ?_ ?_
  · exact original_eq
  · exact stage_eq.trans (congrArg (fun program : Cached.Basic.CachedProgram => program.stage index) original_eq)
  · exact fresh.property.trans (SourceFrontier.Continuous.buildCached_eq _ [] request)

/-- The supplied original program and returned source result assemble to the original complete stage result. -/
theorem assembleWith_eq_build (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (original : Cached.Basic.CachedProgram) (original_eq : original = Program.program policy schedule extraDepth)
    (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult
      (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request) :
    assembleWith policy schedule extraDepth index original original_eq request fresh =
      Source.build policy schedule extraDepth index request :=
  assembleAt_eq_build policy schedule extraDepth index original original_eq _ rfl request fresh

/-- Any returned certified source result assembles to the complete original policy-selected stage result. -/
theorem assemble_eq_build (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult
      (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request) :
    assemble policy schedule extraDepth index request fresh =
      Source.build policy schedule extraDepth index request := by
  exact assembleWith_eq_build policy schedule extraDepth index _ rfl request fresh

/-- The source preparation selected from the same retained selection cache as the original program. -/
@[expose] def retainedPreparation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest) :=
  Preparation.prepare (Horner.Real.finiteModulus (retained.selection index).depth) request

/-- Assemble a source result and supplied stage from the same retained exponential construction.

The supplied source result uses the depth read from the retained selection
entries. The supplied stage is the actual cached model at the retained
index, so no stage query is needed during assembly. -/
@[expose] def assembleRetainedAt {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) : Result policy schedule extraDepth index request := by
  have depth_eq : (retained.selection index).depth = (Selection.selection policy schedule index).depth :=
    congrArg Selection.depth (retained.selection_eq index)
  exact assembleAt policy schedule extraDepth index retained.program retained.program_eq stage stage_eq
    request (depth_eq ▸ fresh)

/-- Assemble a source result with the requested stage from the retained model cache. -/
@[expose] def assembleRetained {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) : Result policy schedule extraDepth index request :=
  assembleRetainedAt retained index (retained.program.stage index) rfl request fresh

/-- A returned-source assembly keeps the exact supplied original stage cache. -/
theorem assembleRetainedAt_stage {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) : (assembleRetainedAt retained index stage stage_eq request fresh).stage = stage := rfl

/-- The supplied stage and returned source result assemble to the complete original stage result. -/
theorem assembleRetainedAt_eq_build {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) :
    assembleRetainedAt retained index stage stage_eq request fresh =
      Source.build policy schedule extraDepth index request := by
  unfold assembleRetainedAt
  exact assembleAt_eq_build policy schedule extraDepth index retained.program retained.program_eq stage stage_eq
    request _

/-- A retained-stage assembly keeps the exact supplied cached program. -/
theorem assembleRetained_program {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) : (assembleRetained retained index request fresh).program = retained.program := rfl

/-- A retained-stage assembly reads its stage from the exact same supplied model cache. -/
theorem assembleRetained_stage {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) : (assembleRetained retained index request fresh).stage = retained.program.stage index := rfl

/-- The retained-cache source and stage assemble to the complete original stage result. -/
theorem assembleRetained_eq_build {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus (retained.selection index).depth)
      [] request) :
    assembleRetained retained index request fresh = Source.build policy schedule extraDepth index request :=
  assembleRetainedAt_eq_build retained index (retained.program.stage index) rfl request fresh

/-- Prepare the finite source from the actual returned selection. -/
@[expose] def selectedPreparation {index : Nat} (selected : Selection index) (request : AccuracyRequest) :=
  Preparation.prepare (Horner.Real.finiteModulus selected.depth) request

/-- Assemble the returned source and model using the same supplied original selection. -/
@[expose] def assembleSelected {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (selected : Selection index) (selected_eq : selected = retained.selection index)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest)
    (fresh : Continuous.Observation.CertifiedResult (Horner.Real.finiteModulus selected.depth) [] request) :
    Result policy schedule extraDepth index request := by
  have depth_eq : selected.depth = (Selection.selection policy schedule index).depth :=
    congrArg Selection.depth (selected_eq.trans (retained.selection_eq index))
  exact assembleAt policy schedule extraDepth index retained.program retained.program_eq stage stage_eq
    request (depth_eq ▸ fresh)

/-- Observe a source construction using the supplied actual selection and original stage model. -/
@[expose] def selectedComputation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (selected : Selection index) (selected_eq : selected = retained.selection index)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest) :
    Program (Continuous.Observation.Entry (selectedPreparation selected request))
      (SourcePoint (Horner.Real.finiteSource selected.depth))
      (Except (Continuous.Observation.InvalidTag (selectedPreparation selected request))
        (Result policy schedule extraDepth index request)) :=
  (Continuous.Observation.certifiedResultComputation (Horner.Real.finiteModulus selected.depth) [] request).map
    fun result => result.map (assembleSelected retained index selected selected_eq stage stage_eq request)

/-- Original replies reconstruct the original stage from the supplied selection and model. -/
theorem selectedComputation_original {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (selected : Selection index) (selected_eq : selected = retained.selection index)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest) :
    ((selectedComputation retained index selected selected_eq stage stage_eq request).protocol.run
      (Continuous.Observation.originalReply (selectedPreparation selected request))).value =
      .ok (Source.build policy schedule extraDepth index request) := by
  unfold selectedComputation selectedPreparation
  rw [Program.map_execution, Protocol.map_run_value, Continuous.Observation.certifiedResult_original]
  apply congrArg Except.ok
  unfold assembleSelected
  exact assembleAt_eq_build policy schedule extraDepth index retained.program retained.program_eq stage stage_eq
    request _

/-- Observe a stage-source construction using the supplied original cached stage.

The selection and source use the same retained selection entries as the
program. The returned source result is assembled with the supplied stage,
so an earlier model observation need not be requested again. -/
@[expose] def retainedComputationAt {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest) :
    Program (Continuous.Observation.Entry (retainedPreparation retained index request))
      (SourcePoint (Horner.Real.finiteSource (retained.selection index).depth))
      (Except (Continuous.Observation.InvalidTag (retainedPreparation retained index request))
        (Result policy schedule extraDepth index request)) :=
  selectedComputation retained index (retained.selection index) rfl stage stage_eq request

/-- Observe a stage-source construction through its exact retained selection and model caches. -/
@[expose] def retainedComputation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest) :
    Program (Continuous.Observation.Entry (retainedPreparation retained index request))
      (SourcePoint (Horner.Real.finiteSource (retained.selection index).depth))
      (Except (Continuous.Observation.InvalidTag (retainedPreparation retained index request))
        (Result policy schedule extraDepth index request)) :=
  retainedComputationAt retained index (retained.program.stage index) rfl request

/-- Original source replies return the original stage result using the exact supplied cached model. -/
theorem retainedComputationAt_original {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest) :
    ((retainedComputationAt retained index stage stage_eq request).protocol.run
      (Continuous.Observation.originalReply (retainedPreparation retained index request))).value =
        .ok (Source.build policy schedule extraDepth index request) := by
  exact selectedComputation_original retained index (retained.selection index) rfl stage stage_eq request

/-- Original source replies return the complete original stage using the retained selection and model caches. -/
theorem retainedComputation_original {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest) :
    ((retainedComputation retained index request).protocol.run
      (Continuous.Observation.originalReply (retainedPreparation retained index request))).value =
        .ok (Source.build policy schedule extraDepth index request) :=
  retainedComputationAt_original retained index (retained.program.stage index) rfl request

/-- Replaying a supplied-stage construction returns the complete original stage without source calls. -/
theorem retainedComputationAt_replay {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest) :
    let program := retainedComputationAt retained index stage stage_eq request
    let oracle := Continuous.Observation.originalReply (retainedPreparation retained index request)
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok (Source.build policy schedule extraDepth index request)) := by
  let program := retainedComputationAt retained index stage stage_eq request
  let oracle := Continuous.Observation.originalReply (retainedPreparation retained index request)
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, retainedComputationAt_original]

/-- Replies outside the supplied-stage source trace preserve its complete result and ordered requests. -/
theorem retainedComputationAt_payload_erasure {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat)
    (stage : Cached.Basic.CachedModel) (stage_eq : stage = retained.program.stage index) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload)
    (outside : Payload → Continuous.Observation.Entry (retainedPreparation retained index request) →
      SourcePoint (Horner.Real.finiteSource (retained.selection index).depth)) :
    let program := retainedComputationAt retained index stage stage_eq request
    let oracle := Continuous.Observation.originalReply (retainedPreparation retained index request)
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (retainedComputationAt retained index stage stage_eq request).protocol.annotation_erasure
    (Continuous.Observation.originalReply (retainedPreparation retained index request)) payload outside

/-- Exact replay recovers the retained-cache stage without repeating its displayed source requests. -/
theorem retainedComputation_replay {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest) :
    let program := retainedComputation retained index request
    let oracle := Continuous.Observation.originalReply (retainedPreparation retained index request)
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok (Source.build policy schedule extraDepth index request)) := by
  let program := retainedComputation retained index request
  let oracle := Continuous.Observation.originalReply (retainedPreparation retained index request)
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, retainedComputation_original]

/-- Replies outside the retained-cache stage's actual source trace preserve its complete execution. -/
theorem retainedComputation_payload_erasure {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) (index : Nat) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload)
    (outside : Payload → Continuous.Observation.Entry (retainedPreparation retained index request) →
      SourcePoint (Horner.Real.finiteSource (retained.selection index).depth)) :
    let program := retainedComputation retained index request
    let oracle := Continuous.Observation.originalReply (retainedPreparation retained index request)
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (retainedComputation retained index request).protocol.annotation_erasure
    (Continuous.Observation.originalReply (retainedPreparation retained index request)) payload outside

/-- Observe the original policy-selected exponential stage and its actual finite Taylor source requests. -/
@[expose] def computation (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest) :
    Program (Continuous.Observation.Entry (preparation policy schedule index request))
      (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
      (Except (Continuous.Observation.InvalidTag (preparation policy schedule index request))
        (Result policy schedule extraDepth index request)) :=
  (Continuous.Observation.certifiedResultComputation
    (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth) [] request).map fun result =>
      result.map (assemble policy schedule extraDepth index request)

/-- Original-source execution returns the complete original cached exponential stage and source result. -/
theorem computation_original (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest) :
    ((computation policy schedule extraDepth index request).protocol.run
      (Continuous.Observation.originalReply (preparation policy schedule index request))).value =
        .ok (Source.build policy schedule extraDepth index request) := by
  unfold computation preparation
  rw [Program.map_execution, Protocol.map_run_value, Continuous.Observation.certifiedResult_original]
  apply congrArg Except.ok
  exact assemble_eq_build policy schedule extraDepth index request _

/-- Exact replay returns the complete original stage result without repeating its displayed source requests. -/
theorem computation_replay (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest) :
    let program := computation policy schedule extraDepth index request
    let oracle := Continuous.Observation.originalReply (preparation policy schedule index request)
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok (Source.build policy schedule extraDepth index request)) := by
  let program := computation policy schedule extraDepth index request
  let oracle := Continuous.Observation.originalReply (preparation policy schedule index request)
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Replies outside the actual displayed stage-source requests preserve the complete result and ordered trace. -/
theorem payload_erasure (policy : Geometry.Policy) (schedule : PositiveStride) (extraDepth index : Nat)
    (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Continuous.Observation.Entry (preparation policy schedule index request) →
      SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)) :
    let program := computation policy schedule extraDepth index request
    let oracle := Continuous.Observation.originalReply (preparation policy schedule index request)
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation policy schedule extraDepth index request).protocol.annotation_erasure
    (Continuous.Observation.originalReply (preparation policy schedule index request)) payload outside

/-- Observe a continued source frontier for the retained original exponential stage.

The selected Taylor depth and original stage remain fixed. Fresh-mesh and
common-point requests use the previous frontier's points and supplied bank;
their returned data build the actual source continuation. -/
@[expose] def continuation {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (_result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) :=
  Continuation.computation (Horner.Real.finiteModulus (Selection.selection policy schedule index).depth)
    previous cached request

/-- Original Taylor-source replies return the exact cache-aware exponential continuation. -/
theorem continuation_original {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) :
    ((continuation result previous cached request).protocol.run
      (Continuation.originalReplyAll (preparation policy schedule index request))).value =
        .ok (result.advanceFrontier previous cached request) :=
  Continuation.computation_original _ previous cached request

/-- Replaying the displayed source replies returns the same retained-stage continuation. -/
theorem continuation_replay {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) :
    let program := continuation result previous cached request
    let oracle := Continuation.originalReplyAll (preparation policy schedule index request)
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok (result.advanceFrontier previous cached request)) :=
  Continuation.computation_replay _ previous cached request

/-- An adequate saved exponential frontier makes no displayed source request. -/
theorem continuation_reused {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {oldRequest : AccuracyRequest} (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) (adequate : (integralBound previous.cells).width < request.tolerance)
    (oracle : Continuation.Query (preparation policy schedule index request) →
      SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)) :
    ((continuation result previous cached request).protocol.run oracle).trace = [] :=
  (Continuation.computation_reused _ previous cached request adequate oracle).2

/-- Replies outside the actual continuation trace preserve its complete result and ordered requests. -/
theorem continuation_payload_erasure {policy : Geometry.Policy} {schedule : PositiveStride}
    {extraDepth index : Nat} {oldRequest : AccuracyRequest}
    (result : Result policy schedule extraDepth index oldRequest)
    (previous : SourceFrontier (Horner.Real.finiteSource (Selection.selection policy schedule index).depth))
    (cached : List (SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)))
    (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Continuation.Query (preparation policy schedule index request) →
      SourcePoint (Horner.Real.finiteSource (Selection.selection policy schedule index).depth)) :
    let program := continuation result previous cached request
    let oracle := Continuation.originalReplyAll (preparation policy schedule index request)
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  Continuation.payload_erasure _ previous cached request payload outside

end Purelib.Integration.Exponential.Program.Source.Observation

end
