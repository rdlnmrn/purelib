module
public import Purelib.Integration.Cell.Numerical.Continuous.Observation
public import Purelib.Integration.Cell.Numerical.Continuous.Producer
public import Purelib.Integration.Cell.Numerical.Common.Observation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing persistent numerical-source requests

The original numerical modulus and retained finite history are fixed inputs.
The fresh mesh and common refinement display their actual point requests.
Common requests carry their actual saved bank so the same returned point state
supplies both indexed parents without reconstructing the fresh producer.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Continuous.Observation.Continuation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat

/-- A fresh-mesh occurrence or a common-child request with its actual point bank. -/
abbrev Query {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) :=
  Sum (Entry prepared) (List (NumericalPoint source) × Common.Observation.Query)

/-- A fresh point reply or a common point reply retaining its actual original bank. -/
abbrev Reply {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :=
  Sum (CachedReply prepared cached)
    (Sigma fun bank : List (NumericalPoint source) => Common.Observation.Reply bank request)

set_option genInjectivity false in
/-- A wrong reply or invalid point occurrence at the numerical continuation boundary. -/
inductive Failure {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) where
  /-- A reply belongs to the other displayed request operation. -/ | operation (requested : Query prepared)
  /-- A common reply carries a point bank other than the actual original bank. -/ | bank
      (requested reported : List (NumericalPoint source)) (different : reported ≠ requested)
  /-- A fresh point reply names the wrong original mesh occurrence. -/ | fresh (invalid : InvalidEntry prepared)
  /-- A common point reply names the wrong original common child. -/ | common (invalid : Common.Observation.Invalid)

constructive_injectivity Failure

/-- The exact bank consumed by the original common refinement after a fresh request. -/
@[expose] def available {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) (fresh : CachedResult modulus) :
    List (NumericalPoint source) :=
  fresh.frontier.cells.map (fun cell => cell.item) ++ previous.cells.map (fun cell => cell.item) ++ cached

/-- Original source replies use the supplied fresh occurrence or actual common point bank. -/
@[expose] def originalReplyAll {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    Query prepared → Reply prepared cached request
  | .inl entry => .inl (originalCachedReply prepared cached entry)
  | .inr (bank, query) => .inr ⟨bank, Common.Observation.originalReply bank request query⟩

/-- Display one original fresh-mesh point request. -/
@[expose] def freshHandler {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (entry : Entry prepared) : Program (Query prepared) (Reply prepared cached request)
      (Except (Failure prepared) (CachedReply prepared cached)) :=
  .request (.inl entry) fun reply => match reply with
    | .inl point => .pure (.ok point)
    | .inr _ => .pure (.error (.operation (.inl entry)))

/-- Compose a fresh numerical result and displayed requests using one retained preparation. -/
@[expose] def freshProgramPrepared {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (prepared : Preparation modulus) (same : prepared = Preparation.prepare modulus request) :
    Program (Query prepared) (Reply prepared cached request) (Except (Failure prepared)
      (Basic.Execution (Entry prepared) (CachedReply prepared cached) (Except (InvalidEntry prepared)
        (CertifiedResult modulus cached request)))) :=
  (certifiedResultPrepared modulus cached request prepared same).substituteChecked
    (freshHandler prepared cached request)

/-- Compose the original cache-aware fresh result with its displayed numerical requests. -/
@[expose] def freshProgram {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (Reply prepared cached request) (Except (Failure prepared)
      (Basic.Execution (Entry prepared) (CachedReply prepared cached) (Except (InvalidEntry prepared)
        (CertifiedResult modulus cached request)))) :=
  freshProgramPrepared modulus cached request (Preparation.prepare modulus request) rfl

/-- Original execution of the fresh program retains the complete original execution and trace. -/
theorem freshProgram_original {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((freshProgram modulus cached request).protocol.run (originalReplyAll prepared cached request)).value =
      .ok ((certifiedResultComputation modulus cached request).protocol.run (originalCachedReply prepared cached)) := by
  let prepared := Preparation.prepare modulus request
  change ((freshProgram modulus cached request).protocol.run (originalReplyAll prepared cached request)).value = _
  unfold freshProgram
  apply Program.substituteChecked_value
  intro entry
  rfl

/-- Display one common-child point request with its actual retained bank. -/
@[expose] def commonHandler {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (bank : List (NumericalPoint source)) (query : Common.Observation.Query) :
    Program (Query prepared) (Reply prepared cached request)
      (Except (Failure prepared) (Common.Observation.Reply bank request)) :=
  .request (.inr (bank, query)) fun reply => match reply with
    | .inl _ => .pure (.error (.operation (.inr (bank, query))))
    | .inr ⟨reported, point⟩ =>
        if same : reported = bank then .pure (.ok (same ▸ point))
        else .pure (.error (.bank bank reported same))

/-- Compose the common refinement with its actual bank-bearing numerical point requests. -/
@[expose] def commonProgram {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (bank : List (NumericalPoint source)) (left right : NumericalFrontier source) :
    Program (Query prepared) (Reply prepared cached request) (Except (Failure prepared)
      (Basic.Execution Common.Observation.Query (Common.Observation.Reply bank request)
        (Except Common.Observation.Invalid (Common.Observation.Certified bank left right request)))) :=
  (Common.Observation.certifiedComputation bank left right request).substituteChecked
    (commonHandler prepared cached request bank)

/-- Original execution of the common program retains its complete selected-bank point execution. -/
theorem commonProgram_original {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (bank : List (NumericalPoint source)) (left right : NumericalFrontier source) :
    ((commonProgram prepared cached request bank left right).protocol.run
      (originalReplyAll prepared cached request)).value =
      .ok ((Common.Observation.certifiedComputation bank left right request).protocol.run
        (Common.Observation.originalReply bank request)) := by
  unfold commonProgram
  apply Program.substituteChecked_value
  intro query
  unfold commonHandler
  change (((if same : bank = bank then
    (Program.pure (.ok (same ▸ Common.Observation.originalReply bank request query)) :
      Program (Query prepared) (Reply prepared cached request)
        (Except (Failure prepared) (Common.Observation.Reply bank request)))
    else Program.pure (.error (.bank bank bank same))).protocol).run
      (originalReplyAll prepared cached request)).value = _
  rewrite [dif_pos rfl]
  rfl

/-- Assemble the actual refined continuation from the returned fresh result and common observations. -/
@[expose] def fromCertified {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (fresh : CertifiedResult modulus (Producer.effectiveBank previous cached) request)
    (common : Common.Observation.Certified (available previous (Producer.effectiveBank previous cached) fresh.val)
      previous fresh.val.frontier request) :
    Producer.Continuation (producer modulus) previous := by
  have split : IntegrationFrontierRefines common.val.intersection.cells previous.cells := by
    rw [common.property]
    exact CommonReadings.commonReadingsCached_intersection_refines previous fresh.val.frontier
      (available previous (Producer.effectiveBank previous cached) fresh.val) request
  exact .refined request cached fresh.val fresh.property common.val split

/-- Returned certified data assemble to the original cache-aware continuation. -/
theorem fromCertified_eq {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (fresh : CertifiedResult modulus (Producer.effectiveBank previous cached) request)
    (common : Common.Observation.Certified (available previous (Producer.effectiveBank previous cached) fresh.val)
      previous fresh.val.frontier request)
    (notAccurate : ¬ (integralBound previous.cells).width < request.tolerance) :
    fromCertified modulus previous cached request fresh common =
      (producer modulus).advanceCached cached previous request := by
  cases fresh with
  | mk fresh fresh_eq =>
    cases fresh_eq
    cases common with
    | mk common common_eq =>
      cases common_eq
      unfold fromCertified Producer.advanceCached Producer.advanceWithBank available
      rw [dif_neg notAccurate]
      rfl

/-- A returned continuation retaining its equality to the original cache-aware request. -/
abbrev CertifiedStep {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :=
  {step : Producer.Continuation (producer modulus) previous //
    step = (producer modulus).advanceCached cached previous request}

/-- Execute a refining numerical request from its retained preparation and point bank.

The equality witnesses connect both supplied objects to the original request;
the executable fresh and common observations consume those supplied objects. -/
@[expose] def certifiedRefiningPrepared {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)] (modulus : Rational.Uniform.Numerical source)
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (prepared : Preparation modulus) (preparedEq : prepared = Preparation.prepare modulus request)
    (effective : List (NumericalPoint source)) (effectiveEq : effective = Producer.effectiveBank previous cached)
    (notAccurate : ¬ (integralBound previous.cells).width < request.tolerance) :
    Program (Query prepared) (Reply prepared effective request)
      (Except (Failure prepared) (CertifiedStep modulus previous cached request)) :=
  (freshProgramPrepared modulus effective request prepared preparedEq).bind fun result =>
    match result with
    | .error invalid => .pure (.error invalid)
    | .ok execution =>
        match execution.value with
        | .error invalid => .pure (.error (.fresh invalid))
        | .ok fresh =>
            let bank := available previous effective fresh.val
            (commonProgram prepared effective request bank previous fresh.val.frontier).map fun result =>
              match result with
              | .error invalid => .error invalid
              | .ok execution =>
                  match execution.value with
                  | .error invalid => .error (.common invalid)
                  | .ok common =>
                      let originalFresh : CertifiedResult modulus (Producer.effectiveBank previous cached) request :=
                        effectiveEq ▸ fresh
                      have sameCommon : Common.Observation.Certified bank previous fresh.val.frontier request =
                          Common.Observation.Certified
                            (available previous (Producer.effectiveBank previous cached) originalFresh.val)
                            previous originalFresh.val.frontier request := by
                        cases effectiveEq
                        rfl
                      let originalCommon := cast sameCommon common
                      .ok ⟨fromCertified modulus previous cached request originalFresh originalCommon,
                        fromCertified_eq modulus previous cached request originalFresh originalCommon notAccurate⟩

/-- Execute the saved numerical request and retain the returned continuation's original ownership. -/
@[expose] def certifiedComputationWithBank {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cachedBank : Unit → List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (Reply prepared (Producer.effectiveBank previous (cachedBank ())) request)
      (Except (Failure prepared) (CertifiedStep modulus previous (cachedBank ()) request)) := by
  if accurate : (integralBound previous.cells).width < request.tolerance then
    have same : (Producer.Continuation.reused request accurate : Producer.Continuation (producer modulus) previous) =
        (producer modulus).advanceCached (cachedBank ()) previous request := by
      unfold Producer.advanceCached Producer.advanceWithBank
      rw [dif_pos accurate]
    exact .pure (.ok ⟨.reused request accurate, same⟩)
  else
    let cached := cachedBank ()
    let effective := Producer.effectiveBank previous cached
    let prepared := Preparation.prepare modulus request
    exact certifiedRefiningPrepared modulus previous cached request prepared rfl effective rfl accurate

/-- Execute the saved numerical request with its supplied cached point bank. -/
@[expose] def certifiedComputation {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)] (modulus : Rational.Uniform.Numerical source)
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (Reply prepared (Producer.effectiveBank previous cached) request)
      (Except (Failure prepared) (CertifiedStep modulus previous cached request)) :=
  certifiedComputationWithBank modulus previous (fun _ => cached) request

/-- Execute a numerical continuation while delaying its bank until refinement is needed. -/
@[expose] def computationWithBank {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)] (modulus : Rational.Uniform.Numerical source)
    (previous : NumericalFrontier source) (cachedBank : Unit → List (NumericalPoint source))
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (Reply prepared (Producer.effectiveBank previous (cachedBank ())) request)
      (Except (Failure prepared) (Producer.Continuation (producer modulus) previous)) :=
  (certifiedComputationWithBank modulus previous cachedBank request).map fun returned => returned.map Subtype.val

/-- Execute the original saved numerical request through its actual point-process observations. -/
@[expose] def computation {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (Reply prepared (Producer.effectiveBank previous cached) request)
      (Except (Failure prepared) (Producer.Continuation (producer modulus) previous)) :=
  (certifiedComputation modulus previous cached request).map fun returned => returned.map Subtype.val

/-- A satisfied saved frontier returns immediately without a numerical point request. -/
theorem computation_reused {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (accurate : (integralBound previous.cells).width < request.tolerance)
    (oracle : Query (Preparation.prepare modulus request) →
      Reply (Preparation.prepare modulus request) (Producer.effectiveBank previous cached) request) :
    ((computation modulus previous cached request).protocol.run oracle).value = .ok (.reused request accurate) ∧
      ((computation modulus previous cached request).protocol.run oracle).trace = [] := by
  unfold computation certifiedComputation certifiedComputationWithBank
  rw [dif_pos accurate]
  exact ⟨rfl, rfl⟩

/-- Original execution returns the certified cache-aware numerical continuation. -/
theorem certifiedComputation_original {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((certifiedComputation modulus previous cached request).protocol.run
      (originalReplyAll prepared (Producer.effectiveBank previous cached) request)).value =
      .ok ⟨(producer modulus).advanceCached cached previous request, rfl⟩ := by
  let prepared := Preparation.prepare modulus request
  change ((certifiedComputation modulus previous cached request).protocol.run
    (originalReplyAll prepared (Producer.effectiveBank previous cached) request)).value = _
  unfold certifiedComputation certifiedComputationWithBank
  by_cases accurate : (integralBound previous.cells).width < request.tolerance
  · rw [dif_pos accurate]
    apply congrArg Except.ok
    apply Subtype.ext
    change Producer.Continuation.reused request accurate = (producer modulus).advanceCached cached previous request
    unfold Producer.advanceCached Producer.advanceWithBank
    rw [dif_pos accurate]
  · rw [dif_neg accurate]
    dsimp only
    unfold certifiedRefiningPrepared
    have freshOriginal := freshProgram_original modulus (Producer.effectiveBank previous cached) request
    unfold freshProgram at freshOriginal
    rw [Program.bind_execution, Protocol.bind_run_value, freshOriginal]
    dsimp only
    rw [certifiedResult_original]
    rw [Program.map_execution, Protocol.map_run_value, commonProgram_original]
    dsimp only
    rw [Common.Observation.certified_original]
    apply congrArg Except.ok
    apply Subtype.ext
    exact fromCertified_eq modulus previous cached request _ _ accurate

/-- Original execution returns the complete cache-aware numerical continuation. -/
theorem computation_original {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((computation modulus previous cached request).protocol.run
      (originalReplyAll prepared (Producer.effectiveBank previous cached) request)).value =
      .ok ((producer modulus).advanceCached cached previous request) := by
  change (((certifiedComputation modulus previous cached request).map fun returned =>
    returned.map Subtype.val).protocol.run
      (originalReplyAll (Preparation.prepare modulus request)
        (Producer.effectiveBank previous cached) request)).value = _
  rw [Program.map_execution, Protocol.map_run_value, certifiedComputation_original]
  rfl

/-- Exact replay returns the complete numerical continuation without repeating its displayed requests. -/
theorem computation_replay {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := computation modulus previous cached request
    program.protocol.replayExact
      (program.protocol.run (originalReplyAll prepared (Producer.effectiveBank previous cached) request)).trace =
      .ok (.ok ((producer modulus).advanceCached cached previous request)) := by
  let prepared := Preparation.prepare modulus request
  let program := computation modulus previous cached request
  change program.protocol.replayExact
    (program.protocol.run (originalReplyAll prepared (Producer.effectiveBank previous cached) request)).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Changes outside the displayed point requests preserve the complete continuation and ordered trace. -/
theorem payload_erasure {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (previous : NumericalFrontier source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Query (Preparation.prepare modulus request) →
      Reply (Preparation.prepare modulus request) (Producer.effectiveBank previous cached) request) :
    let prepared := Preparation.prepare modulus request
    let program := computation modulus previous cached request
    program.protocol.run (Boundary.Trace.overlay
      (program.protocol.run (originalReplyAll prepared (Producer.effectiveBank previous cached) request)).trace
      (outside payload)) = program.protocol.run (originalReplyAll prepared (Producer.effectiveBank previous cached)
        request) :=
  (computation modulus previous cached request).protocol.annotation_erasure
    (originalReplyAll (Preparation.prepare modulus request) (Producer.effectiveBank previous cached) request)
    payload outside

/-- A returned numerical history retaining its equality to the original persistent request. -/
abbrev CertifiedState {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :=
  {next : (producer modulus).integrationProcess.State //
    next = (producer modulus).integrationProcess.request state request.tolerance request.positive}

/-- Observe a persistent request and retain the actual returned history with its original ownership. -/
@[expose] def certifiedHistoryComputation {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)] (modulus : Rational.Uniform.Numerical source)
    (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared)
      (Reply prepared (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2)) request)
      (Except (Failure prepared) (CertifiedState modulus state request)) :=
  (certifiedComputationWithBank modulus state.1
    (fun _ => (producer modulus).retainedReadings state.2) request).map fun returned =>
    returned.map fun step =>
      ⟨⟨step.val.frontier, RefiningController.History.next state.2 step.val⟩,
        congrArg (fun continuation : Producer.Continuation (producer modulus) state.1 =>
          (⟨continuation.frontier, RefiningController.History.next state.2 continuation⟩ :
            (producer modulus).integrationProcess.State)) step.property⟩

/-- Original execution retains the original persistent state as the returned certified history. -/
theorem certifiedHistoryComputation_original {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)] (modulus : Rational.Uniform.Numerical source)
    (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let cached := (producer modulus).retainedReadings state.2
    ((certifiedHistoryComputation modulus state request).protocol.run
      (originalReplyAll prepared (Producer.effectiveBank state.1 cached) request)).value =
      .ok ⟨(producer modulus).integrationProcess.request state request.tolerance request.positive, rfl⟩ := by
  unfold certifiedHistoryComputation
  dsimp only
  have original := certifiedComputation_original modulus state.1 ((producer modulus).retainedReadings state.2) request
  unfold certifiedComputation at original
  rw [Program.map_execution, Protocol.map_run_value, original]
  rfl

/-- Observe the public persistent numerical request from its actual retained history. -/
@[expose] def historyComputation {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared)
      (Reply prepared (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2)) request)
      (Except (Failure prepared) (producer modulus).integrationProcess.State) :=
  (computationWithBank modulus state.1
    (fun _ => (producer modulus).retainedReadings state.2) request).map fun returned =>
    returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩

/-- Continue a persistent refining request from its retained preparation and point bank.

The supplied preparation and effective bank belong to this same request and
history; the resulting program retains the original continuation and state. -/
@[expose] def historyRefiningPrepared {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)] (modulus : Rational.Uniform.Numerical source)
    (state : (producer modulus).integrationProcess.State) (request : AccuracyRequest)
    (prepared : Preparation modulus) (preparedEq : prepared = Preparation.prepare modulus request)
    (cached : List (NumericalPoint source))
    (_cachedEq : cached = (producer modulus).retainedReadings state.2)
    (effective : List (NumericalPoint source)) (effectiveEq : effective = Producer.effectiveBank state.1 cached)
    (notAccurate : ¬ (integralBound state.1.cells).width < request.tolerance) :
    Program (Query prepared) (Reply prepared effective request)
      (Except (Failure prepared) (producer modulus).integrationProcess.State) :=
  ((certifiedRefiningPrepared modulus state.1 cached request prepared preparedEq effective effectiveEq notAccurate).map
    fun returned => returned.map Subtype.val).map fun returned =>
      returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩

/-- Original execution returns the complete next public numerical integration state. -/
theorem historyComputation_original {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let cached := (producer modulus).retainedReadings state.2
    ((historyComputation modulus state request).protocol.run
      (originalReplyAll prepared (Producer.effectiveBank state.1 cached) request)).value =
      .ok ((producer modulus).integrationProcess.request state request.tolerance request.positive) := by
  let prepared := Preparation.prepare modulus request
  let cached := (producer modulus).retainedReadings state.2
  change (((computation modulus state.1 cached request).map fun returned =>
    returned.map fun step => (⟨step.frontier, RefiningController.History.next state.2 step⟩ :
      (producer modulus).integrationProcess.State)).protocol.run
      (originalReplyAll prepared (Producer.effectiveBank state.1 cached) request)).value = _
  rw [Program.map_execution, Protocol.map_run_value, computation_original]
  rfl

/-- Exact replay recovers the complete public numerical integration history. -/
theorem historyComputation_replay {source : Fraction.Rational → BoundProcess} [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let cached := (producer modulus).retainedReadings state.2
    let program := historyComputation modulus state request
    program.protocol.replayExact
      (program.protocol.run (originalReplyAll prepared (Producer.effectiveBank state.1 cached) request)).trace =
      .ok (.ok ((producer modulus).integrationProcess.request state request.tolerance request.positive)) := by
  let prepared := Preparation.prepare modulus request
  let cached := (producer modulus).retainedReadings state.2
  let program := historyComputation modulus state request
  change program.protocol.replayExact
    (program.protocol.run (originalReplyAll prepared (Producer.effectiveBank state.1 cached) request)).trace = _
  rw [program.protocol.replayExact_run, historyComputation_original]

/-- Replies outside the public numerical request trace preserve its complete state and ordered trace. -/
theorem historyComputation_payload_erasure {source : Fraction.Rational → BoundProcess}
    [DecidableEq (NumericalPoint source)]
    (modulus : Rational.Uniform.Numerical source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Query (Preparation.prepare modulus request) →
      Reply (Preparation.prepare modulus request)
        (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2)) request) :
    let prepared := Preparation.prepare modulus request
    let cached := (producer modulus).retainedReadings state.2
    let program := historyComputation modulus state request
    program.protocol.run (Boundary.Trace.overlay
      (program.protocol.run (originalReplyAll prepared (Producer.effectiveBank state.1 cached) request)).trace
      (outside payload)) = program.protocol.run (originalReplyAll prepared (Producer.effectiveBank state.1 cached)
        request) :=
  (historyComputation modulus state request).protocol.annotation_erasure
    (originalReplyAll (Preparation.prepare modulus request)
      (Producer.effectiveBank state.1 ((producer modulus).retainedReadings state.2)) request)
    payload outside

end Purelib.Integration.NumericalFrontier.Continuous.Observation.Continuation

end
