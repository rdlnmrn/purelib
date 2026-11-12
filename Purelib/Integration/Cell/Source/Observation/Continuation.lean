module
public import Purelib.Integration.Cell.Source.Observation
public import Purelib.Integration.Cell.Source.Producer
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing persistent exact-source producer requests

A concrete producer supplies its actual finite fresh-result query program.
The continuation exposes its cached common-point reads and builds the original
intersection from their returned values. The original source and producer
preparation remain fixed inputs.
-/

public section

namespace Purelib.Integration.SourceFrontier.Observation.Continuation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- A fresh partition occurrence or one rational common-refinement tag. -/
abbrev Query (partition : Unit.Normalized) := Sum (Entry partition) Fraction.Rational

set_option genInjectivity false in
/-- An invalid source reply at a fresh or common rational point. -/
inductive Failure (partition : Unit.Normalized) where
  /-- The fresh reply carries the wrong tag. -/ | source (invalid : InvalidTag partition)
  /-- The common reply carries the wrong tag. -/ | common
      (requested reported : Fraction.Rational) (different : reported ≠ requested)

constructive_injectivity Failure

/-- Read the original source at any displayed rational tag. -/
@[expose] def originalPoint (source : Fraction.Rational → Fraction.Rational) (point : Fraction.Rational) :
    SourcePoint source :=
  SourcePoint.observe source ⟨point, point⟩ point le_rfl le_rfl

/-- Run the original source at either the fresh-mesh or common-point boundary. -/
@[expose] def originalReplyAll {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) : Query partition → SourcePoint source
  | .inl entry => SourceFrontier.Observation.originalReply source partition entry
  | .inr point => originalPoint source point

/-- Read one common rational tag from the saved bank or from one displayed source request. -/
@[expose] def commonPoint {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (cached : List (SourcePoint source))
    (point : Fraction.Rational) : Program (Query partition) (SourcePoint source)
      (Except (Failure partition) {retained : SourcePoint source // retained.point = point}) :=
  match SourcePoint.findCached cached point with
  | some retained => .pure (.ok retained)
  | none => .request (.inr point) fun reply =>
      if same : reply.point = point then .pure (.ok ⟨reply, same⟩)
      else .pure (.error (.common point reply.point same))

/-- The point selected by the original source and saved bank at a common tag. -/
@[expose] def originalCommonPoint {source : Fraction.Rational → Fraction.Rational}
    (cached : List (SourcePoint source)) (point : Fraction.Rational) :
    {retained : SourcePoint source // retained.point = point} :=
  match SourcePoint.findCached cached point with
  | some retained => retained
  | none => ⟨originalPoint source point, rfl⟩

/-- The common-point program returns the actual bank hit or original source reply. -/
theorem commonPoint_original {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (cached : List (SourcePoint source))
    (point : Fraction.Rational) :
    ((commonPoint partition cached point).protocol.run (originalReplyAll partition)).value =
      .ok (originalCommonPoint cached point) := by
  unfold commonPoint originalCommonPoint
  cases found : SourcePoint.findCached cached point with
  | some retained => rfl
  | none =>
      change (((if same : (originalPoint source point).point = point then
        (Program.pure (.ok ⟨originalPoint source point, same⟩) :
          Program (Query partition) (SourcePoint source)
            (Except (Failure partition) {retained : SourcePoint source // retained.point = point}))
        else Program.pure (.error (.common point (originalPoint source point).point same))).protocol).run
          (originalReplyAll partition)).value = _
      have same : (originalPoint source point).point = point := rfl
      rewrite [dif_pos same]
      rfl

/-- One indexed child occurrence of an already retained common refinement. -/
abbrev CommonEntry {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :=
  {entry // entry ∈ refinement.entries}

/-- Every retained common child is a valid unit interval. -/
theorem commonValid {source : Fraction.Rational → Fraction.Rational} {left right : SourceFrontier source}
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entry : CommonEntry left right refinement) :
    entry.val.child.Valid := by
  have member : entry.val.child ∈ refinement.partition.intervals := by
    rw [← refinement.children_eq]
    exact (Purelib.Data.List.Map.mem_map).mpr ⟨entry.val, entry.property, rfl⟩
  exact refinement.partition.valid entry.val.child member

/-- The original common-child reading at its own left endpoint. -/
@[expose] def originalCommon {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entry : CommonEntry left right refinement) :
    CommonReading left right :=
  readCommon left right entry.val (commonValid refinement entry) entry.val.child.start
    ⟨le_rfl, (commonValid refinement entry).2.1.le⟩

/-- Build one common child directly from the returned exact reading at its tag. -/
@[expose] def returnedCommon {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entry : CommonEntry left right refinement)
    (point : {retained : SourcePoint source // retained.point = entry.val.child.start}) : CommonReading left right :=
  readCommonWith left right (cachedPair [point.val]) entry.val (commonValid refinement entry) entry.val.child.start
    ⟨le_rfl, (commonValid refinement entry).2.1.le⟩

/-- The returned point supplies the same original common child and both indexed parents. -/
theorem returnedCommon_eq {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entry : CommonEntry left right refinement)
    (point : {retained : SourcePoint source // retained.point = entry.val.child.start}) :
    returnedCommon left right refinement entry point = originalCommon left right refinement entry :=
  readCommonWith_eq left right (cachedPair [point.val]) entry.val (commonValid refinement entry) entry.val.child.start
    ⟨le_rfl, (commonValid refinement entry).2.1.le⟩

/-- Ordered returned common children certified against their exact original indexed occurrences. -/
abbrev CommonBatch {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entries : List (CommonEntry left right refinement)) :=
  {readings : List (CommonReading left right) // readings = entries.map (originalCommon left right refinement)}

/-- Add one returned common point to the already returned ordered common children. -/
@[expose] def prependCommon {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entry : CommonEntry left right refinement)
    (remaining : List (CommonEntry left right refinement))
    (point : {retained : SourcePoint source // retained.point = entry.val.child.start})
    (tail : CommonBatch left right refinement remaining) : CommonBatch left right refinement (entry :: remaining) :=
  ⟨returnedCommon left right refinement entry point :: tail.val,
    congrArg₂ List.cons (returnedCommon_eq left right refinement entry point) tail.property⟩

/-- Observe each common child using its actual retained or returned source point. -/
@[expose] def commonBatch {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    (entries : List (CommonEntry left right refinement)) → Program (Query partition) (SourcePoint source)
      (Except (Failure partition) (CommonBatch left right refinement entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining =>
      (commonPoint partition cached entry.val.child.start).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (commonBatch partition cached left right refinement remaining).map
            (fun after => after.map (prependCommon left right refinement entry remaining point))

/-- Original-source common-point execution returns all original children in their indexed order. -/
theorem commonBatch_original {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    ∀ entries : List (CommonEntry left right refinement),
      ((commonBatch partition cached left right refinement entries).protocol.run (originalReplyAll partition)).value =
        .ok ⟨entries.map (originalCommon left right refinement), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((commonPoint partition cached entry.val.child.start).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (commonBatch partition cached left right refinement remaining).map
            (fun after => after.map (prependCommon left right refinement entry remaining point))).protocol.run
          (originalReplyAll partition)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, commonPoint_original]
      rw [Program.map_execution, Protocol.map_run_value,
        commonBatch_original partition cached left right refinement remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      change returnedCommon left right refinement entry (originalCommonPoint cached entry.val.child.start) :: _ = _
      rewrite [returnedCommon_eq]
      rfl

/-- Assemble the common refinement from the returned certified children without another source read. -/
@[expose] def assembleCommon {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (returned : CommonBatch left right (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach) : CommonReadings left right := by
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  have entries_eq : returned.val.map CommonReading.entry = refinement.entries := by
    rw [returned.property, Purelib.Data.List.Map.map_map]
    change refinement.entries.attach.map Subtype.val = refinement.entries
    exact Purelib.Data.List.attach_map_subtype_val _
  exact ⟨refinement, returned.val, entries_eq⟩

/-- Returned common children assemble to the exact original common refinement. -/
theorem assembleCommon_eq {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (returned : CommonBatch left right (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach) :
    assembleCommon left right returned = commonReadings left right := by
  refine CommonReadings.ext _ _ ?_ ?_
  · rfl
  · exact returned.property

/-- A returned common refinement certified as the original common construction. -/
abbrev CertifiedCommon {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source) :=
  {common : CommonReadings left right // common = commonReadings left right}

/-- Return the original common refinement from its actual cached or returned source readings. -/
@[expose] def certifiedCommon {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) :
    Program (Query partition) (SourcePoint source) (Except (Failure partition) (CertifiedCommon left right)) :=
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  (commonBatch partition cached left right refinement refinement.entries.attach).map fun returned =>
    returned.map fun batch => ⟨assembleCommon left right batch, assembleCommon_eq left right batch⟩

/-- Original-source common execution returns the exact original indexed common refinement. -/
theorem certifiedCommon_original {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) :
    ((certifiedCommon partition cached left right).protocol.run (originalReplyAll partition)).value =
      .ok ⟨commonReadings left right, rfl⟩ := by
  unfold certifiedCommon
  rw [Program.map_execution, Protocol.map_run_value, commonBatch_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assembleCommon_eq left right _


/-- A fresh output certified as the exact cache-aware request of the original producer. -/
abbrev Fresh {source : Fraction.Rational → Fraction.Rational} (producer : Producer source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :=
  {output : producer.Output // output = producer.requestCached cached request}

/-- Display an actual fresh partition occurrence within the composed continuation. -/
@[expose] def freshHandler {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (entry : Entry partition) : Program (Query partition) (SourcePoint source) (Except Empty (SourcePoint source)) :=
  (Program.query (.inl entry)).map Except.ok

/-- Compose an original certified fresh construction with its displayed source requests. -/
@[expose] def freshProgram {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer cached request))) :
    Program (Query partition) (SourcePoint source) (Except Empty
      (Basic.Execution (Entry partition) (SourcePoint source) (Except (InvalidTag partition)
        (Fresh producer cached request)))) :=
  fresh.substituteChecked (freshHandler partition)

/-- Fresh composition retains the complete original fresh execution and its ordered trace. -/
theorem freshProgram_original {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer cached request))) :
    ((freshProgram partition producer cached request fresh).protocol.run (originalReplyAll partition)).value =
      .ok (fresh.protocol.run (SourceFrontier.Observation.originalReply source partition)) := by
  unfold freshProgram
  apply Program.substituteChecked_value
  intro entry
  unfold freshHandler
  rw [Program.map_execution, Protocol.map_run_value]
  rfl

/-- Assemble a refined continuation from the actual returned fresh result and common readings. -/
@[expose] def fromCertified {source : Fraction.Rational → Fraction.Rational} (producer : Producer source)
    (previous : SourceFrontier source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (fresh : Fresh producer (Producer.effectiveBank previous cached) request)
    (common : CertifiedCommon previous (producer.frontier fresh.val)) :
    Producer.Continuation producer previous := by
  have split : IntegrationFrontierRefines common.val.intersection.cells previous.cells := by
    rw [common.property]
    exact CommonReadings.commonReadings_intersection_refines previous (producer.frontier fresh.val)
  exact .refined request cached fresh.val fresh.property common.val split

/-- The returned certified data assemble to the original cache-aware producer continuation. -/
theorem fromCertified_eq {source : Fraction.Rational → Fraction.Rational} (producer : Producer source)
    (previous : SourceFrontier source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (fresh : Fresh producer (Producer.effectiveBank previous cached) request)
    (common : CertifiedCommon previous (producer.frontier fresh.val))
    (notAccurate : ¬ (integralBound previous.cells).width < request.tolerance) :
    fromCertified producer previous cached request fresh common = producer.advanceCached cached previous request := by
  cases fresh with
  | mk fresh fresh_eq =>
    cases fresh_eq
    cases common with
    | mk common common_eq =>
      let fresh := producer.requestCached (Producer.effectiveBank previous cached) request
      let available := (producer.frontier fresh).cells.map (fun cell => cell.item) ++
        previous.cells.map (fun cell => cell.item) ++ Producer.effectiveBank previous cached
      have same : common = commonReadingsCached previous (producer.frontier fresh) available :=
        common_eq.trans (commonReadingsCached_eq previous (producer.frontier fresh) available).symm
      cases same
      unfold fromCertified Producer.advanceCached Producer.advanceWithBank
      rw [dif_neg notAccurate]

/-- Compose a refining continuation from one retained observation bank and fresh program.

The effective bank is linked to the original cached readings and is supplied
to both the fresh construction and the common refinement without rebuilding it. -/
@[expose] def refiningPrepared {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) (effective : List (SourcePoint source))
    (effectiveEq : effective = Producer.effectiveBank previous cached)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer effective request))) :
    Program (Query partition) (SourcePoint source)
      (Except (Failure partition) (Producer.Continuation producer previous)) :=
  (freshProgram partition producer effective request fresh).bind fun result =>
    match result with
    | .error impossible => nomatch impossible
    | .ok execution =>
        match execution.value with
        | .error invalid => .pure (.error (.source invalid))
        | .ok returned =>
            let available := (producer.frontier returned.val).cells.map (fun cell => cell.item) ++
              previous.cells.map (fun cell => cell.item) ++ effective
            (certifiedCommon partition available previous (producer.frontier returned.val)).map fun common =>
              common.map fun common => by
                have split : IntegrationFrontierRefines common.val.intersection.cells previous.cells := by
                  rw [common.property]
                  exact CommonReadings.commonReadings_intersection_refines previous (producer.frontier returned.val)
                exact .refined request cached returned.val
                  (returned.property.trans (congrArg (fun bank => producer.requestCached bank request) effectiveEq))
                  common.val split

/-- Compose a concrete original fresh program with the cached common refinement and saved frontier. -/
@[expose] def computation {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer (Producer.effectiveBank previous cached) request))) :
    Program (Query partition) (SourcePoint source)
      (Except (Failure partition) (Producer.Continuation producer previous)) := by
  if accurate : (integralBound previous.cells).width < request.tolerance then
    exact .pure (.ok (.reused request accurate))
  else
    exact refiningPrepared partition producer previous cached request
      (Producer.effectiveBank previous cached) rfl fresh

/-- An already accurate saved frontier returns without any displayed source request. -/
theorem computation_reused {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer (Producer.effectiveBank previous cached) request)))
    (accurate : (integralBound previous.cells).width < request.tolerance)
    (oracle : Query partition → SourcePoint source) :
    ((computation partition producer previous cached request fresh).protocol.run oracle).value =
      .ok (.reused request accurate) ∧
      ((computation partition producer previous cached request fresh).protocol.run oracle).trace = [] := by
  unfold computation
  rw [dif_pos accurate]
  exact ⟨rfl, rfl⟩

/-- Original-source execution returns the original continuation when the concrete fresh program returns its output. -/
theorem computation_original {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer (Producer.effectiveBank previous cached) request)))
    (freshOriginal : (fresh.protocol.run (SourceFrontier.Observation.originalReply source partition)).value =
      .ok ⟨producer.requestCached (Producer.effectiveBank previous cached) request, rfl⟩) :
    ((computation partition producer previous cached request fresh).protocol.run (originalReplyAll partition)).value =
      .ok (producer.advanceCached cached previous request) := by
  unfold computation
  by_cases accurate : (integralBound previous.cells).width < request.tolerance
  · rw [dif_pos accurate]
    unfold Producer.advanceCached Producer.advanceWithBank
    rw [dif_pos accurate]
    rfl
  · rw [dif_neg accurate]
    unfold refiningPrepared
    rw [Program.bind_execution, Protocol.bind_run_value, freshProgram_original]
    dsimp only
    rw [freshOriginal]
    rw [Program.map_execution, Protocol.map_run_value, certifiedCommon_original]
    apply congrArg Except.ok
    exact fromCertified_eq producer previous cached request _ _ accurate

/-- Exact replay recovers the complete original continuation without repeating displayed source requests. -/
theorem computation_replay {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer (Producer.effectiveBank previous cached) request)))
    (freshOriginal : (fresh.protocol.run (SourceFrontier.Observation.originalReply source partition)).value =
      .ok ⟨producer.requestCached (Producer.effectiveBank previous cached) request, rfl⟩) :
    (computation partition producer previous cached request fresh).protocol.replayExact
      ((computation partition producer previous cached request fresh).protocol.run (originalReplyAll partition)).trace =
        .ok (.ok (producer.advanceCached cached previous request)) := by
  rw [(computation partition producer previous cached request fresh).protocol.replayExact_run,
    computation_original partition producer previous cached request fresh freshOriginal]

/-- Replies outside the executed continuation trace preserve its complete result and ordered trace. -/
theorem payload_erasure {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer (Producer.effectiveBank previous cached) request)))
    {Payload : Type} (payload : Payload) (outside : Payload → Query partition → SourcePoint source) :
    (computation partition producer previous cached request fresh).protocol.run (Boundary.Trace.overlay
      ((computation partition producer previous cached request fresh).protocol.run (originalReplyAll partition)).trace
      (outside payload)) =
      (computation partition producer previous cached request fresh).protocol.run (originalReplyAll partition) :=
  (computation partition producer previous cached request fresh).protocol.annotation_erasure
    (originalReplyAll partition) payload outside

/-- Continue a refining history using its actual retained and effective banks.

The equalities identify the supplied banks with the saved history and its
frontier. The fresh program and common construction consume the same bank. -/
@[expose] def historyRefiningPrepared {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (producer : Producer source) (state : producer.integrationProcess.State)
    (request : AccuracyRequest) (cached : List (SourcePoint source))
    (_cachedEq : cached = producer.retainedReadings state.2) (effective : List (SourcePoint source))
    (effectiveEq : effective = Producer.effectiveBank state.1 cached)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Fresh producer effective request))) :
    Program (Query partition) (SourcePoint source) (Except (Failure partition) producer.integrationProcess.State) :=
  (refiningPrepared partition producer state.1 cached request effective effectiveEq fresh).map fun returned =>
    returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩

/-- Observe a persistent request, deferring its fresh program until refinement is needed.

The callback receives the actual saved and effective banks with their exact
ownership equalities. An already accurate frontier does not evaluate it. -/
@[expose] def historyComputationWithBank {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (producer : Producer source) (state : producer.integrationProcess.State)
    (request : AccuracyRequest)
    (fresh : (cached : List (SourcePoint source)) → cached = producer.retainedReadings state.2 →
      (effective : List (SourcePoint source)) → effective = Producer.effectiveBank state.1 cached →
      Program (Entry partition) (SourcePoint source)
        (Except (InvalidTag partition) (Fresh producer effective request))) :
    Program (Query partition) (SourcePoint source) (Except (Failure partition) producer.integrationProcess.State) := by
  if accurate : (integralBound state.1.cells).width < request.tolerance then
    exact .pure (.ok ⟨state.1, RefiningController.History.next state.2 (.reused request accurate)⟩)
  else
    let cached := producer.retainedReadings state.2
    let effective := Producer.effectiveBank state.1 cached
    exact historyRefiningPrepared partition producer state request cached rfl effective rfl
      (fresh cached rfl effective rfl)

/-- Observe a public persistent request from its actual retained history and concrete fresh program. -/
@[expose] def historyComputation {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (state : producer.integrationProcess.State) (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition)
        (Fresh producer (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request))) :
    Program (Query partition) (SourcePoint source) (Except (Failure partition) producer.integrationProcess.State) := by
  if accurate : (integralBound state.1.cells).width < request.tolerance then
    exact .pure (.ok ⟨state.1, RefiningController.History.next state.2 (.reused request accurate)⟩)
  else
    let cached := producer.retainedReadings state.2
    exact (computation partition producer state.1 cached request fresh).map fun returned =>
      returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩

/-- The deferred history agrees with the original composed continuation on both branches. -/
theorem historyComputation_eq {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (state : producer.integrationProcess.State) (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition)
        (Fresh producer (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request))) :
    historyComputation partition producer state request fresh =
      (computation partition producer state.1 (producer.retainedReadings state.2) request fresh).map
        (fun returned => returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩) := by
  unfold historyComputation
  by_cases accurate : (integralBound state.1.cells).width < request.tolerance
  · rw [dif_pos accurate]
    unfold computation
    rw [dif_pos accurate]
    rfl
  · rw [dif_neg accurate]
    rfl

/-- Original execution returns the complete next public source-integration state. -/
theorem historyComputation_original {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (state : producer.integrationProcess.State) (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition)
        (Fresh producer (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request)))
    (freshOriginal : (fresh.protocol.run (SourceFrontier.Observation.originalReply source partition)).value =
      .ok ⟨producer.requestCached (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request, rfl⟩) :
    ((historyComputation partition producer state request fresh).protocol.run (originalReplyAll partition)).value =
      .ok (producer.integrationProcess.request state request.tolerance request.positive) := by
  rw [historyComputation_eq]
  let cached := producer.retainedReadings state.2
  change (((computation partition producer state.1 cached request fresh).map fun returned =>
    returned.map fun step => (⟨step.frontier, RefiningController.History.next state.2 step⟩ :
      producer.integrationProcess.State)).protocol.run (originalReplyAll partition)).value = _
  rw [Program.map_execution, Protocol.map_run_value,
    computation_original partition producer state.1 cached request fresh freshOriginal]
  rfl

/-- Exact replay recovers the complete public source-integration history. -/
theorem historyComputation_replay {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (producer : Producer source) (state : producer.integrationProcess.State) (request : AccuracyRequest)
    (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition)
        (Fresh producer (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request)))
    (freshOriginal : (fresh.protocol.run (SourceFrontier.Observation.originalReply source partition)).value =
      .ok ⟨producer.requestCached (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request, rfl⟩) :
    (historyComputation partition producer state request fresh).protocol.replayExact
      ((historyComputation partition producer state request fresh).protocol.run (originalReplyAll partition)).trace =
        .ok (.ok (producer.integrationProcess.request state request.tolerance request.positive)) := by
  rw [(historyComputation partition producer state request fresh).protocol.replayExact_run,
    historyComputation_original partition producer state request fresh freshOriginal]

/-- Replies outside the public request trace preserve the complete next state and ordered trace. -/
theorem historyComputation_payload_erasure {source : Fraction.Rational → Fraction.Rational}
    (partition : Unit.Normalized) (producer : Producer source) (state : producer.integrationProcess.State)
    (request : AccuracyRequest) (fresh : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition)
        (Fresh producer (Producer.effectiveBank state.1 (producer.retainedReadings state.2)) request)))
    {Payload : Type} (payload : Payload) (outside : Payload → Query partition → SourcePoint source) :
    (historyComputation partition producer state request fresh).protocol.run (Boundary.Trace.overlay
      ((historyComputation partition producer state request fresh).protocol.run (originalReplyAll partition)).trace
      (outside payload)) =
      (historyComputation partition producer state request fresh).protocol.run (originalReplyAll partition) :=
  (historyComputation partition producer state request fresh).protocol.annotation_erasure
    (originalReplyAll partition) payload outside

end Purelib.Integration.SourceFrontier.Observation.Continuation

end
