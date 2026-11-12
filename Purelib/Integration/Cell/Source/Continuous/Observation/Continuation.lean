module
public import Purelib.Integration.Cell.Source.Continuous.Observation
public import Purelib.Integration.Cell.Source.Continuous.Producer
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing persistent continuous exact-source requests

The original request, saved frontier and point bank are fixed inputs. A
continuation exposes missing source readings for the fresh mesh and common
refinement, retaining every returned point in the construction that consumes
it. Source laws and the finite modulus preparation remain fixed inputs.
-/

public section

namespace Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- A fresh-mesh occurrence or one rational common-refinement tag. -/
abbrev Query {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) := Sum (Entry prepared) Fraction.Rational

set_option genInjectivity false in
/-- An invalid exact source reply at one of the two displayed request boundaries. -/
inductive Failure {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) where
  /-- A fresh-mesh reply has a tag different from its original interval start. -/ | source
      (invalid : InvalidTag prepared)
  /-- A common-point reply has a tag different from the requested rational tag. -/ | common
      (requested reported : Fraction.Rational) (different : reported ≠ requested)

constructive_injectivity Failure

/-- Read the original source at any displayed rational tag. -/
@[expose] def originalPoint (source : Fraction.Rational → Fraction.Rational) (point : Fraction.Rational) :
    SourcePoint source :=
  SourcePoint.observe source ⟨point, point⟩ point le_rfl le_rfl

/-- Run the original source at either the fresh-mesh or common-point boundary. -/
@[expose] def originalReplyAll {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) : Query prepared → SourcePoint source
  | .inl entry => originalReply prepared entry
  | .inr point => originalPoint source point

/-- Read one common rational tag from the saved bank or from one displayed source request. -/
@[expose] def commonPoint {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (point : Fraction.Rational) : Program (Query prepared) (SourcePoint source)
      (Except (Failure prepared) {retained : SourcePoint source // retained.point = point}) :=
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
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (point : Fraction.Rational) :
    ((commonPoint prepared cached point).protocol.run (originalReplyAll prepared)).value =
      .ok (originalCommonPoint cached point) := by
  unfold commonPoint originalCommonPoint
  cases found : SourcePoint.findCached cached point with
  | some retained => rfl
  | none =>
      change (((if same : (originalPoint source point).point = point then
        (Program.pure (.ok ⟨originalPoint source point, same⟩) :
          Program (Query prepared) (SourcePoint source)
            (Except (Failure prepared) {retained : SourcePoint source // retained.point = point}))
        else Program.pure (.error (.common point (originalPoint source point).point same))).protocol).run
          (originalReplyAll prepared)).value = _
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
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    (entries : List (CommonEntry left right refinement)) → Program (Query prepared) (SourcePoint source)
      (Except (Failure prepared) (CommonBatch left right refinement entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining =>
      (commonPoint prepared cached entry.val.child.start).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (commonBatch prepared cached left right refinement remaining).map
            (fun after => after.map (prependCommon left right refinement entry remaining point))

/-- Original-source common-point execution returns all original children in their indexed order. -/
theorem commonBatch_original {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    ∀ entries : List (CommonEntry left right refinement),
      ((commonBatch prepared cached left right refinement entries).protocol.run (originalReplyAll prepared)).value =
        .ok ⟨entries.map (originalCommon left right refinement), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((commonPoint prepared cached entry.val.child.start).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (commonBatch prepared cached left right refinement remaining).map
            (fun after => after.map (prependCommon left right refinement entry remaining point))).protocol.run
          (originalReplyAll prepared)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, commonPoint_original]
      rw [Program.map_execution, Protocol.map_run_value,
        commonBatch_original prepared cached left right refinement remaining]
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
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) :
    Program (Query prepared) (SourcePoint source) (Except (Failure prepared) (CertifiedCommon left right)) :=
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  (commonBatch prepared cached left right refinement refinement.entries.attach).map fun returned =>
    returned.map fun batch => ⟨assembleCommon left right batch, assembleCommon_eq left right batch⟩

/-- Original-source common execution returns the exact original indexed common refinement. -/
theorem certifiedCommon_original {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (left right : SourceFrontier source) :
    ((certifiedCommon prepared cached left right).protocol.run (originalReplyAll prepared)).value =
      .ok ⟨commonReadings left right, rfl⟩ := by
  unfold certifiedCommon
  rw [Program.map_execution, Protocol.map_run_value, commonBatch_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assembleCommon_eq left right _

/-- Display one original fresh-mesh request within the composed continuation boundary. -/
@[expose] def freshHandler {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (entry : Entry prepared) :
    Program (Query prepared) (SourcePoint source) (Except Empty (SourcePoint source)) :=
  (Program.query (.inl entry)).map Except.ok

/-- Compose a fresh result and displayed source requests using one retained preparation. -/
@[expose] def freshProgramPrepared {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (prepared : Preparation modulus) (same : prepared = Preparation.prepare modulus request) :
    Program (Query prepared) (SourcePoint source) (Except Empty
      (Basic.Execution (Entry prepared) (SourcePoint source) (Except (InvalidTag prepared)
        (CertifiedResult modulus cached request)))) :=
  (certifiedResultPrepared modulus cached request prepared same).substituteChecked (freshHandler prepared)

/-- Compose the actual cache-aware fresh result with its displayed rational source requests. -/
@[expose] def freshProgram {source : Fraction.Rational → Fraction.Rational} (modulus : Rational.Uniform.Modulus source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (SourcePoint source) (Except Empty
      (Basic.Execution (Entry prepared) (SourcePoint source) (Except (InvalidTag prepared)
        (CertifiedResult modulus cached request)))) :=
  freshProgramPrepared modulus cached request (Preparation.prepare modulus request) rfl

/-- Fresh composition retains the complete original execution and its ordered outer source trace. -/
theorem freshProgram_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((freshProgram modulus cached request).protocol.run (originalReplyAll prepared)).value =
      .ok ((certifiedResultComputation modulus cached request).protocol.run (originalReply prepared)) := by
  let prepared := Preparation.prepare modulus request
  change ((freshProgram modulus cached request).protocol.run (originalReplyAll prepared)).value = _
  unfold freshProgram
  apply Program.substituteChecked_value
  intro entry
  unfold freshHandler
  rw [Program.map_execution, Protocol.map_run_value]
  rfl

/-- Assemble one actual refined continuation from the returned producer result and common observations. -/
@[expose] def fromCertified {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) (fresh : CertifiedResult modulus (Producer.effectiveBank previous cached) request)
    (common : CertifiedCommon previous fresh.val.frontier) :
    Producer.Continuation (producer modulus) previous := by
  have split : IntegrationFrontierRefines common.val.intersection.cells previous.cells := by
    rw [common.property]
    exact CommonReadings.commonReadings_intersection_refines previous fresh.val.frontier
  exact .refined request cached fresh.val fresh.property common.val split

/-- The assembled continuation is the exact result of the original cache-aware producer request. -/
theorem fromCertified_eq_advance {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) (fresh : CertifiedResult modulus (Producer.effectiveBank previous cached) request)
    (common : CertifiedCommon previous fresh.val.frontier)
    (notAccurate : ¬ (integralBound previous.cells).width < request.tolerance) :
    fromCertified modulus previous cached request fresh common =
      (producer modulus).advanceCached cached previous request := by
  cases fresh with
  | mk fresh fresh_eq =>
    cases fresh_eq
    cases common with
    | mk common common_eq =>
      let fresh := buildCached modulus (Producer.effectiveBank previous cached) request
      let available := fresh.frontier.cells.map (fun cell => cell.item) ++
        previous.cells.map (fun cell => cell.item) ++ Producer.effectiveBank previous cached
      have same : common = commonReadingsCached previous fresh.frontier available :=
        common_eq.trans (commonReadingsCached_eq previous fresh.frontier available).symm
      cases same
      unfold fromCertified Producer.advanceCached Producer.advanceWithBank
      rw [dif_neg notAccurate]
      rfl

/-- A returned continuation certified against the original cache-aware producer request. -/
abbrev CertifiedStep {source : Fraction.Rational → Fraction.Rational} (modulus : Rational.Uniform.Modulus source)
    (previous : SourceFrontier source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :=
  {step : Producer.Continuation (producer modulus) previous //
    step = (producer modulus).advanceCached cached previous request}

/-- Execute the original continuous producer continuation through its actual rational source requests.

A satisfied request returns the saved frontier without a source request.
Otherwise the fresh cache-aware result supplies the original common mesh;
returned common points supply both indexed parents and the intersection.
The original modulus and finite preparation are fixed inputs. -/
@[expose] def certifiedComputationWithBank {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source)
    (cachedBank : Unit → List (SourcePoint source))
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (SourcePoint source)
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
    exact (freshProgramPrepared modulus effective
      request prepared rfl).bind fun result =>
      match result with
      | .error impossible => nomatch impossible
      | .ok execution =>
          match execution.value with
          | .error invalid => .pure (.error (.source invalid))
          | .ok fresh =>
              let available := fresh.val.frontier.cells.map (fun cell => cell.item) ++
                previous.cells.map (fun cell => cell.item) ++ effective
              (certifiedCommon prepared available previous fresh.val.frontier).map fun common =>
                common.map fun returned =>
                  ⟨fromCertified modulus previous cached request fresh returned,
                    fromCertified_eq_advance modulus previous cached request fresh returned accurate⟩

/-- Execute the original continuation with the supplied cached point bank. -/
@[expose] def certifiedComputation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (SourcePoint source)
      (Except (Failure prepared) (CertifiedStep modulus previous cached request)) :=
  certifiedComputationWithBank modulus previous (fun _ => cached) request

/-- Execute a continuation while delaying its retained bank until refinement is needed. -/
@[expose] def computationWithBank {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source)
    (cachedBank : Unit → List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (SourcePoint source)
      (Except (Failure prepared) (Producer.Continuation (producer modulus) previous)) :=
  (certifiedComputationWithBank modulus previous cachedBank request).map fun returned => returned.map Subtype.val

/-- Execute the original continuation through its exact returned source observations. -/
@[expose] def computation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (SourcePoint source)
      (Except (Failure prepared) (Producer.Continuation (producer modulus) previous)) :=
  (certifiedComputation modulus previous cached request).map fun returned => returned.map Subtype.val

/-- A satisfied saved frontier returns immediately with an empty source trace. -/
theorem computation_reused {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) (accurate : (integralBound previous.cells).width < request.tolerance)
    (oracle : Query (Preparation.prepare modulus request) → SourcePoint source) :
    ((computation modulus previous cached request).protocol.run oracle).value = .ok (.reused request accurate) ∧
      ((computation modulus previous cached request).protocol.run oracle).trace = [] := by
  unfold computation certifiedComputation certifiedComputationWithBank
  rw [dif_pos accurate]
  exact ⟨rfl, rfl⟩

/-- A successful refined execution retains the fresh requests followed by its actual common-point requests. -/
theorem computation_refined_trace {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) (notAccurate : ¬ (integralBound previous.cells).width < request.tolerance)
    (oracle : Query (Preparation.prepare modulus request) → SourcePoint source)
    (outer : Basic.Execution (Entry (Preparation.prepare modulus request)) (SourcePoint source)
      (Except (InvalidTag (Preparation.prepare modulus request))
        (CertifiedResult modulus (Producer.effectiveBank previous cached) request)))
    (fresh : CertifiedResult modulus (Producer.effectiveBank previous cached) request)
    (freshRun : ((freshProgram modulus (Producer.effectiveBank previous cached) request).protocol.run oracle).value =
      .ok outer)
    (success : outer.value = .ok fresh) :
    let available := fresh.val.frontier.cells.map (fun cell => cell.item) ++
      previous.cells.map (fun cell => cell.item) ++ Producer.effectiveBank previous cached
    ((computation modulus previous cached request).protocol.run oracle).trace =
      ((freshProgram modulus (Producer.effectiveBank previous cached) request).protocol.run oracle).trace ++
        ((certifiedCommon (Preparation.prepare modulus request) available previous fresh.val.frontier).protocol.run
          oracle).trace := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_trace]
  unfold certifiedComputation certifiedComputationWithBank
  rw [dif_neg notAccurate]
  dsimp only
  unfold freshProgram at freshRun ⊢
  rw [Program.bind_execution, Protocol.bind_run_trace, freshRun]
  dsimp only
  rw [success]
  rw [Program.map_execution, Protocol.map_run_trace]

/-- Original-source execution returns the certified cache-aware producer continuation. -/
theorem certifiedComputation_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((certifiedComputation modulus previous cached request).protocol.run (originalReplyAll prepared)).value =
      .ok ⟨(producer modulus).advanceCached cached previous request, rfl⟩ := by
  let prepared := Preparation.prepare modulus request
  change ((certifiedComputation modulus previous cached request).protocol.run (originalReplyAll prepared)).value = _
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
    have freshOriginal := freshProgram_original modulus (Producer.effectiveBank previous cached) request
    unfold freshProgram at freshOriginal
    rw [Program.bind_execution, Protocol.bind_run_value, freshOriginal]
    dsimp only
    rw [certifiedResult_original]
    rw [Program.map_execution, Protocol.map_run_value, certifiedCommon_original]
    apply congrArg Except.ok
    apply Subtype.ext
    exact fromCertified_eq_advance modulus previous cached request _ _ accurate

/-- Original-source execution returns the complete actual continuous producer continuation. -/
theorem computation_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((computation modulus previous cached request).protocol.run (originalReplyAll prepared)).value =
      .ok ((producer modulus).advanceCached cached previous request) := by
  change (((certifiedComputation modulus previous cached request).map fun returned =>
    returned.map Subtype.val).protocol.run
      (originalReplyAll (Preparation.prepare modulus request))).value = _
  rw [Program.map_execution, Protocol.map_run_value, certifiedComputation_original]
  rfl

/-- Exact replay returns the complete original continuation without repeating its displayed source requests. -/
theorem computation_replay {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := computation modulus previous cached request
    program.protocol.replayExact (program.protocol.run (originalReplyAll prepared)).trace =
      .ok (.ok ((producer modulus).advanceCached cached previous request)) := by
  let prepared := Preparation.prepare modulus request
  let program := computation modulus previous cached request
  change program.protocol.replayExact (program.protocol.run (originalReplyAll prepared)).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Changes outside the actual displayed source requests preserve the complete continuation and ordered trace. -/
theorem payload_erasure {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (previous : SourceFrontier source) (cached : List (SourcePoint source))
    (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Query (Preparation.prepare modulus request) → SourcePoint source) :
    let prepared := Preparation.prepare modulus request
    let program := computation modulus previous cached request
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (originalReplyAll prepared)).trace
      (outside payload)) = program.protocol.run (originalReplyAll prepared) :=
  (computation modulus previous cached request).protocol.annotation_erasure
    (originalReplyAll (Preparation.prepare modulus request)) payload outside

/-- Observe one request of the public persistent integration process from its actual retained history. -/
@[expose] def historyComputation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Query prepared) (SourcePoint source)
      (Except (Failure prepared) (producer modulus).integrationProcess.State) :=
  (computationWithBank modulus state.1
    (fun _ => (producer modulus).retainedReadings state.2) request).map fun returned =>
    returned.map fun step => ⟨step.frontier, RefiningController.History.next state.2 step⟩

/-- Original-source execution returns the complete state produced by the public persistent integration request. -/
theorem historyComputation_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((historyComputation modulus state request).protocol.run (originalReplyAll prepared)).value =
      .ok ((producer modulus).integrationProcess.request state request.tolerance request.positive) := by
  let prepared := Preparation.prepare modulus request
  let cached := (producer modulus).retainedReadings state.2
  change (((computation modulus state.1 cached request).map fun returned =>
    returned.map fun step => (⟨step.frontier, RefiningController.History.next state.2 step⟩ :
      (producer modulus).integrationProcess.State)).protocol.run
      (originalReplyAll prepared)).value = _
  rw [Program.map_execution, Protocol.map_run_value, computation_original]
  rfl

/-- Exact replay returns the complete public integration state without repeating the displayed source requests. -/
theorem historyComputation_replay {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := historyComputation modulus state request
    program.protocol.replayExact (program.protocol.run (originalReplyAll prepared)).trace =
      .ok (.ok ((producer modulus).integrationProcess.request state request.tolerance request.positive)) := by
  let prepared := Preparation.prepare modulus request
  let program := historyComputation modulus state request
  change program.protocol.replayExact (program.protocol.run (originalReplyAll prepared)).trace = _
  rw [program.protocol.replayExact_run, historyComputation_original]

/-- Replies outside the displayed public request trace preserve its complete state and ordered trace. -/
theorem historyComputation_payload_erasure {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (state : (producer modulus).integrationProcess.State)
    (request : AccuracyRequest) {Payload : Type} (payload : Payload)
    (outside : Payload → Query (Preparation.prepare modulus request) → SourcePoint source) :
    let prepared := Preparation.prepare modulus request
    let program := historyComputation modulus state request
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (originalReplyAll prepared)).trace
      (outside payload)) = program.protocol.run (originalReplyAll prepared) :=
  (historyComputation modulus state request).protocol.annotation_erasure
    (originalReplyAll (Preparation.prepare modulus request)) payload outside

end Purelib.Integration.SourceFrontier.Continuous.Observation.Continuation

end
