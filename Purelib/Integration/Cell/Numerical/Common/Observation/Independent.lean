module

public import Purelib.Integration.Cell.Numerical.Common.Operational.Observation
public import Purelib.Computation.Query.Program.CertifiedBatch
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing independent numerical common-point readings

Each common child retains both original frontier owners. Its two point
observations use those owners' actual saved states and rational tags; a
separate joint comparison can then consume the returned observations.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Common.Observation.Independent

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- One retained occurrence in the original common partition. -/
abbrev Occurrence {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) :=
  {entry // entry ∈ (Unit.Common.commonRefinement left.partition right.partition).entries}

/-- The exact ordered occurrences in the original common partition. -/
@[expose] def occurrences {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) : List (Occurrence left right) :=
  (Unit.Common.commonRefinement left.partition right.partition).entries.attach

/-- An index preserves the original occurrence even when child intervals coincide. -/
abbrev Index {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) :=
  Fin (occurrences left right).length

/-- The original indexed common child and its membership certificate. -/
@[expose] def entry {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (index : Index left right) :=
  (occurrences left right).get index

/-- Every original common occurrence is a valid positive-length unit interval. -/
theorem occurrenceValid {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (occurrence : Occurrence left right) :
    occurrence.val.child.Valid := by
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  have member : occurrence.val.child ∈ refinement.partition.intervals := by
    rw [← refinement.children_eq]
    exact (Purelib.Data.List.Map.mem_map).mpr ⟨occurrence.val, occurrence.property, rfl⟩
  exact refinement.partition.valid _ member

/-- Every indexed original common child is a valid positive-length unit interval. -/
theorem entryValid {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (index : Index left right) :
    (entry left right index).val.child.Valid := occurrenceValid left right (entry left right index)

/-- The original left parent point for one indexed common child. -/
@[expose] def leftParent {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (index : Index left right) :
    NumericalPoint leftSource :=
  (left.partitioned.cellAtOwner (entry left right index).val.leftOwner).val.item

/-- The original right parent point for one indexed common child. -/
@[expose] def rightParent {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (index : Index left right) :
    NumericalPoint rightSource :=
  (right.partitioned.cellAtOwner (entry left right index).val.rightOwner).val.item

/-- The exact left observation selected at the common child's original starting tag. -/
@[expose] def leftPoint {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) : NumericalPoint leftSource :=
  (leftParent left right index).retag (entry left right index).val.child (entry left right index).val.child.start
    le_rfl (entryValid left right index).2.1.le request

/-- The exact right observation selected at the common child's original starting tag. -/
@[expose] def rightPoint {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) : NumericalPoint rightSource :=
  (rightParent left right index).retag (entry left right index).val.child (entry left right index).val.child.start
    le_rfl (entryValid left right index).2.1.le request

/-- A returned left point is certified against its original owner and indexed child. -/
abbrev LeftSelected {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) := {point : NumericalPoint leftSource // point = leftPoint left right request index}

/-- A returned right point is certified against its original owner and indexed child. -/
abbrev RightSelected {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) := {point : NumericalPoint rightSource // point = rightPoint left right request index}

/-- A displayed request identifies one original owner and occurrence. -/
abbrev Query {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) :=
  Sum (Index left right) (Index left right)

set_option genInjectivity false in
/-- A left point reply carries the original common-occurrence index. -/
structure LeftReply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) where
  /-- The actual original common occurrence. -/ index : Index left right
  /-- The point returned for that occurrence. -/ point : LeftSelected left right request index

constructive_injectivity LeftReply

set_option genInjectivity false in
/-- A right point reply carries the original common-occurrence index. -/
structure RightReply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) where
  /-- The actual original common occurrence. -/ index : Index left right
  /-- The point returned for that occurrence. -/ point : RightSelected left right request index

constructive_injectivity RightReply

/-- Replies retain which original source owner produced the point. -/
abbrev Reply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :=
  Sum (LeftReply left right request) (RightReply left right request)

set_option genInjectivity false in
/-- A returned point identifies the wrong source owner or common occurrence. -/
inductive Failure {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) where
  /-- The reply belongs to the other original source. -/ | owner (requested : Query left right)
  /-- The returned original occurrence differs from the requested occurrence. -/ | index
      (requested reported : Index left right) (different : reported ≠ requested)

constructive_injectivity Failure

/-- The two original sources answer their own indexed point requests. -/
@[expose] def originalReply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    Query left right → Reply left right request
  | .inl index => .inl ⟨index, ⟨leftPoint left right request index, rfl⟩⟩
  | .inr index => .inr ⟨index, ⟨rightPoint left right request index, rfl⟩⟩

/-- The original common occurrence makes both parent-point observations at its starting tag. -/
@[expose] def occurrenceChild {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (occurrence : Occurrence left right) : CommonReading left right request :=
  readCommon left right request occurrence.val (occurrenceValid left right occurrence)
    occurrence.val.child.start ⟨le_rfl, (occurrenceValid left right occurrence).2.1.le⟩

/-- The indexed original common child retains both original parent observations. -/
@[expose] def originalChild {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) : CommonReading left right request :=
  occurrenceChild left right request (entry left right index)

/-- Assemble one original common child from its two returned original-owner points. -/
@[expose] def returnedChild {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) (first : LeftSelected left right request index)
    (second : RightSelected left right request index) : CommonReading left right request :=
  readCommonFromPair left right request (entry left right index).val (entryValid left right index)
    (entry left right index).val.child.start ⟨le_rfl, (entryValid left right index).2.1.le⟩
    ⟨leftParent left right index, first.val, first.property, rightParent left right index, second.val, second.property⟩

/-- The returned points build the same original common child and retain both parent occurrences. -/
theorem returnedChild_eq {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) (first : LeftSelected left right request index)
    (second : RightSelected left right request index) :
    returnedChild left right request index first second = originalChild left right request index := by
  cases first with
  | mk first first_eq =>
    cases second with
    | mk second second_eq =>
      cases first_eq
      cases second_eq
      rfl

/-- Ordered common children certified against their actual original occurrence indices. -/
abbrev Batch {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (indices : List (Index left right)) :=
  {readings : List (CommonReading left right request) // readings = indices.map (originalChild left right request)}

/-- Prepend the returned observations to the already returned common children. -/
@[expose] def prepend {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) (remaining : List (Index left right))
    (first : LeftSelected left right request index) (second : RightSelected left right request index)
    (tail : Batch left right request remaining) : Batch left right request (index :: remaining) :=
  ⟨returnedChild left right request index first second :: tail.val,
    congrArg₂ List.cons (returnedChild_eq left right request index first second) tail.property⟩

/-- Every ordered indexed occurrence rebuilds exactly the original common refinement's readings. -/
theorem originalChildren {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    (Purelib.Data.List.indices (occurrences left right)).map (originalChild left right request) =
      (commonReadings left right request).readings := by
  change (Purelib.Data.List.indices (occurrences left right)).map
    ((occurrenceChild left right request) ∘ (occurrences left right).get) = _
  rw [← Purelib.Data.List.Map.map_map, Purelib.Data.List.indices_get]
  rfl

/-- Execute a retained point decision, consuming a returned point only for a requested branch. -/
@[expose] def pointWithDecision {source : Fraction.Rational → BoundProcess} {Question Reply Error : Type}
    (interval : Partition.Interval) (tag : Fraction.Rational)
    (start_le : interval.start ≤ tag) (point_le_finish : tag ≤ interval.finish) (request : AccuracyRequest)
    (decision : NumericalPoint.Selection source tag request) (target : NumericalPoint source)
    (targetEq : (decision.resolve interval start_le point_le_finish).val = target) (question : Question)
    (decode : Reply → Except Error {point : NumericalPoint source // point = target}) :
    Program Question Reply (Except Error {point : NumericalPoint source // point = target}) := by
  cases decision with
  | reuse retained same accurate =>
      let selected := retained.move interval tag start_le point_le_finish same
      have selectedEq : selected = target := targetEq
      exact .pure (.ok ⟨selected, selectedEq⟩)
  | request _ => exact .request question fun response => .pure (decode response)

/-- Original replies give the exact target of a retained point decision. -/
theorem pointWithDecision_original {source : Fraction.Rational → BoundProcess} {Question Reply Error : Type}
    [DecidableEq Question] (interval : Partition.Interval) (tag : Fraction.Rational)
    (start_le : interval.start ≤ tag) (point_le_finish : tag ≤ interval.finish) (request : AccuracyRequest)
    (decision : NumericalPoint.Selection source tag request) (target : NumericalPoint source)
    (targetEq : (decision.resolve interval start_le point_le_finish).val = target) (question : Question)
    (decode : Reply → Except Error {point : NumericalPoint source // point = target}) (oracle : Question → Reply)
    (response : decode (oracle question) = .ok ⟨target, rfl⟩) :
    let program := pointWithDecision interval tag start_le point_le_finish request decision target targetEq
      question decode
    (program.protocol.run oracle).value = .ok ⟨target, rfl⟩ := by
  cases decision with
  | reuse retained same accurate =>
      apply congrArg Except.ok
      apply Subtype.ext
      exact targetEq
  | request previous => exact response

/-- Reuse a sufficient parent point or consume a returned observation of its actual retag request.

The original retag's selection determines whether a source request is needed.
The saved branch consumes its retained point; the requested branch consumes the
returned reply without repeating the point request. -/
@[expose] def point {source : Fraction.Rational → BoundProcess} {Question Reply Error : Type}
    (retained : NumericalPoint source) (interval : Partition.Interval) (tag : Fraction.Rational)
    (start_le : interval.start ≤ tag) (point_le_finish : tag ≤ interval.finish) (request : AccuracyRequest)
    (question : Question)
    (decode : Reply → Except Error
      {point : NumericalPoint source // point = retained.retag interval tag start_le point_le_finish request}) :
    Program Question Reply (Except Error
      {point : NumericalPoint source // point = retained.retag interval tag start_le point_le_finish request}) :=
  pointWithDecision interval tag start_le point_le_finish request (retained.selectSaved tag request)
    (retained.retag interval tag start_le point_le_finish request)
    (NumericalPoint.selectSaved_resolve_eq_retag retained interval tag start_le point_le_finish request) question decode

/-- An original point reply returns the exact original retag, including its selected predecessor and readback. -/
theorem point_original {source : Fraction.Rational → BoundProcess} {Question Reply Error : Type}
    [DecidableEq Question] (retained : NumericalPoint source) (interval : Partition.Interval)
    (tag : Fraction.Rational) (start_le : interval.start ≤ tag) (point_le_finish : tag ≤ interval.finish)
    (request : AccuracyRequest) (question : Question)
    (decode : Reply → Except Error
      {point : NumericalPoint source // point = retained.retag interval tag start_le point_le_finish request})
    (oracle : Question → Reply)
    (response : decode (oracle question) =
      .ok ⟨retained.retag interval tag start_le point_le_finish request, rfl⟩) :
    ((point retained interval tag start_le point_le_finish request question decode).protocol.run oracle).value =
      .ok ⟨retained.retag interval tag start_le point_le_finish request, rfl⟩ := by
  exact pointWithDecision_original interval tag start_le point_le_finish request
    (retained.selectSaved tag request) (retained.retag interval tag start_le point_le_finish request)
    (NumericalPoint.selectSaved_resolve_eq_retag retained interval tag start_le point_le_finish request)
    question decode oracle response

/-- Decode a left reply only for the original requested owner and occurrence. -/
@[expose] def decodeLeft {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) (reply : Reply left right request) :
    Except (Failure left right) (LeftSelected left right request index) :=
  match reply with
  | .inr _ => .error (.owner (.inl index))
  | .inl returned =>
      if same : returned.index = index then .ok (same ▸ returned.point)
      else .error (.index index returned.index same)

/-- Decode a right reply only for the original requested owner and occurrence. -/
@[expose] def decodeRight {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) (reply : Reply left right request) :
    Except (Failure left right) (RightSelected left right request index) :=
  match reply with
  | .inl _ => .error (.owner (.inr index))
  | .inr returned =>
      if same : returned.index = index then .ok (same ▸ returned.point)
      else .error (.index index returned.index same)

/-- Observe the original left parent point at its retained common occurrence. -/
@[expose] def leftRequest {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) : Program (Query left right) (Reply left right request)
      (Except (Failure left right) (LeftSelected left right request index)) :=
  point (leftParent left right index) (entry left right index).val.child
    (entry left right index).val.child.start le_rfl (entryValid left right index).2.1.le request
    (.inl index) (decodeLeft left right request index)

/-- Observe the original right parent point at its retained common occurrence. -/
@[expose] def rightRequest {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) : Program (Query left right) (Reply left right request)
      (Except (Failure left right) (RightSelected left right request index)) :=
  point (rightParent left right index) (entry left right index).val.child
    (entry left right index).val.child.start le_rfl (entryValid left right index).2.1.le request
    (.inr index) (decodeRight left right request index)

/-- Original execution returns the exact left parent-point observation. -/
theorem leftRequest_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) :
    ((leftRequest left right request index).protocol.run (originalReply left right request)).value =
      .ok ⟨leftPoint left right request index, rfl⟩ := by
  apply point_original
  change decodeLeft left right request index
    (.inl ⟨index, ⟨leftPoint left right request index, rfl⟩⟩) =
      .ok ⟨leftPoint left right request index, rfl⟩
  unfold decodeLeft
  dsimp only
  rw [dif_pos rfl]

/-- Original execution returns the exact right parent-point observation. -/
theorem rightRequest_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) :
    ((rightRequest left right request index).protocol.run (originalReply left right request)).value =
      .ok ⟨rightPoint left right request index, rfl⟩ := by
  apply point_original
  change decodeRight left right request index
    (.inr ⟨index, ⟨rightPoint left right request index, rfl⟩⟩) =
      .ok ⟨rightPoint left right request index, rfl⟩
  unfold decodeRight
  dsimp only
  rw [dif_pos rfl]

/-- A pair of returned points retains the two original owners at one common occurrence. -/
abbrev SelectedPair {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) := LeftSelected left right request index × RightSelected left right request index

/-- Observe the left and right original parent points in their actual construction order. -/
@[expose] def pair {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) : Program (Query left right) (Reply left right request)
      (Except (Failure left right) (SelectedPair left right request index)) :=
  (leftRequest left right request index).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok first => (rightRequest left right request index).map fun second => second.map fun second => (first, second)

/-- Original execution returns the two original parent-point observations in order. -/
theorem pair_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (index : Index left right) :
    ((pair left right request index).protocol.run (originalReply left right request)).value =
      .ok (⟨leftPoint left right request index, rfl⟩, ⟨rightPoint left right request index, rfl⟩) := by
  unfold pair
  rw [Program.bind_execution, Protocol.bind_run_value, leftRequest_original]
  rw [Program.map_execution, Protocol.map_run_value, rightRequest_original]
  rfl

/-- Observe common occurrences in order, stopping at the first invalid point reply. -/
@[expose] def batch {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (pair : (index : Index left right) → Program (Query left right) (Reply left right request)
      (Except (Failure left right) (SelectedPair left right request index)))
    (indices : List (Index left right)) : Program (Query left right) (Reply left right request)
      (Except (Failure left right) (Batch left right request indices)) :=
  Program.certifiedBatch (originalChild left right request) (SelectedPair left right request)
    (fun index points => returnedChild left right request index points.1 points.2)
    (fun index points => returnedChild_eq left right request index points.1 points.2) (fun _ _ failure => failure)
    pair indices

/-- Original point replies build every requested common child in its original order. -/
theorem batch_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (pair : (index : Index left right) → Program (Query left right) (Reply left right request)
      (Except (Failure left right) (SelectedPair left right request index)))
    (oracle : Query left right → Reply left right request)
    (correct : ∀ index, ((pair index).protocol.run oracle).value =
      .ok (⟨leftPoint left right request index, rfl⟩, ⟨rightPoint left right request index, rfl⟩))
    (indices : List (Index left right)) :
    ((batch left right request pair indices).protocol.run oracle).value =
      .ok ⟨indices.map (originalChild left right request), rfl⟩ :=
  Program.certifiedBatch_original (originalChild left right request) (SelectedPair left right request)
    (fun index points => returnedChild left right request index points.1 points.2)
    (fun index points => returnedChild_eq left right request index points.1 points.2) (fun _ _ failure => failure)
    pair oracle
    (fun index => (⟨leftPoint left right request index, rfl⟩, ⟨rightPoint left right request index, rfl⟩))
    correct indices

/-- Construct the original common refinement from its returned point observations. -/
@[expose] def assemble {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (returned : Batch left right request (Purelib.Data.List.indices (occurrences left right))) :
    CommonReadings left right request := by
  have entries_eq : returned.val.map CommonReading.entry =
      (Unit.Common.commonRefinement left.partition right.partition).entries := by
    rw [returned.property, originalChildren]
    exact (commonReadings left right request).entries_eq
  exact ⟨Unit.Common.commonRefinement left.partition right.partition, returned.val, entries_eq⟩

/-- Returned observations assemble to the complete original independently read common refinement. -/
theorem assemble_eq {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    (returned : Batch left right request (Purelib.Data.List.indices (occurrences left right))) :
    assemble left right request returned = commonReadings left right request := by
  refine CommonReadings.ext _ _ rfl ?_
  exact returned.property.trans (originalChildren left right request)

/-- Observe the original independent common readings in their actual occurrence order. -/
@[expose] def computation {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    Program (Query left right) (Reply left right request)
      (Except (Failure left right) (CommonReadings left right request)) :=
  (batch left right request (pair left right request) (Purelib.Data.List.indices (occurrences left right))).map
    fun result => result.map (assemble left right request)

/-- Original owner replies construct the complete original independently read common refinement. -/
theorem computation_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    ((computation left right request).protocol.run (originalReply left right request)).value =
      .ok (commonReadings left right request) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value,
    batch_original left right request (pair left right request) (originalReply left right request)
      (pair_original left right request)]
  apply congrArg Except.ok
  exact assemble_eq left right request _

/-- Exact replay returns the complete common refinement without repeating either point source. -/
theorem computation_replay {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    (computation left right request).protocol.replayExact
      ((computation left right request).protocol.run (originalReply left right request)).trace =
        .ok (.ok (commonReadings left right request)) := by
  rw [(computation left right request).protocol.replayExact_run, computation_original]

/-- Replies outside the actual owner-specific request trace preserve its complete returned refinement and trace. -/
theorem payload_erasure {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload) (outside : Payload → Query left right → Reply left right request) :
    (computation left right request).protocol.run (Boundary.Trace.overlay
      ((computation left right request).protocol.run (originalReply left right request)).trace (outside payload)) =
      (computation left right request).protocol.run (originalReply left right request) :=
  (computation left right request).protocol.annotation_erasure (originalReply left right request) payload outside

/-- An original occurrence paired with the actual returned common reading for that occurrence. -/
abbrev Tagged {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :=
  Σ index : Index left right, {reading : CommonReading left right request //
    reading = originalChild left right request index}

/-- Original occurrence indices decide equality of their certified common readings. -/
instance {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest} :
    DecidableEq (Tagged left right request) := by
  intro first second
  cases first with
  | mk firstIndex firstReading =>
    cases second with
    | mk secondIndex secondReading =>
      by_cases sameIndex : firstIndex = secondIndex
      · cases sameIndex
        have sameReading : firstReading = secondReading :=
          Subtype.ext (firstReading.property.trans secondReading.property.symm)
        cases sameReading
        exact isTrue rfl
      · exact isFalse (fun equal => sameIndex (congrArg Sigma.fst equal))

/-- Attach each retained common reading to its own original occurrence index. -/
@[expose] def tag {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    (indices : List (Index left right)) → Batch left right request indices → List (Tagged left right request) := by
  intro indices
  induction indices with
  | nil =>
      intro _
      exact []
  | cons index remaining induction =>
      intro returned
      cases returned with
      | mk readings same =>
        cases readings with
        | nil => cases same
        | cons reading tail =>
            have headEq : reading = originalChild left right request index := (List.cons.inj same).1
            have tailEq : tail = remaining.map (originalChild left right request) := (List.cons.inj same).2
            exact ⟨index, ⟨reading, headEq⟩⟩ :: induction ⟨tail, tailEq⟩

/-- Tagging preserves the exact returned common readings and their original order. -/
theorem tag_readings {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :
    ∀ (indices : List (Index left right)) (returned : Batch left right request indices),
      (tag left right request indices returned).map (fun entry => entry.2.val) = returned.val := by
  intro indices
  induction indices with
  | nil =>
      intro returned
      cases returned with
      | mk readings same =>
        cases readings with
        | nil => rfl
        | cons _ _ => cases same
  | cons index remaining induction =>
      intro returned
      cases returned with
      | mk readings same =>
        cases readings with
        | nil => cases same
        | cons reading tail =>
            change reading :: (tag left right request remaining ⟨tail, (List.cons.inj same).2⟩).map
              (fun entry => entry.2.val) = reading :: tail
            exact congrArg (List.cons reading) (induction ⟨tail, (List.cons.inj same).2⟩)

namespace Joint

/-- An original point request or a joint request carrying its actual returned common reading. -/
abbrev Query {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) :=
  Sum (Independent.Query left right) (Tagged left right request)

/-- A joint scheduler result certified for the same returned common reading. -/
abbrev Selected {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (child : Tagged left right request) :=
  {result : JointReading left right request budget //
    result = jointForReading budget equivalent leftCoherent rightCoherent child.2.val}

set_option genInjectivity false in
/-- A returned joint scheduler state and the actual common reading it consumes. -/
structure JointReply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) where
  /-- The actual original common occurrence and returned reading. -/ child : Tagged left right request
  /-- The joint scheduler result for that same reading. -/ result :
    Selected left right request budget equivalent leftCoherent rightCoherent child

constructive_injectivity JointReply

/-- A reply belongs to an original point request or to a joint scheduler request. -/
abbrev Reply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :=
  Sum (Independent.Reply left right request)
    (JointReply left right request budget equivalent leftCoherent rightCoherent)

set_option genInjectivity false in
/-- A point or joint reply is invalid at its original operation or occurrence. -/
inductive Failure {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request : AccuracyRequest) where
  /-- The reply belongs to the other displayed operation. -/ | operation (requested : Query left right request)
  /-- A point reply has the wrong original owner or occurrence. -/ | point (invalid : Independent.Failure left right)
  /-- A joint reply names a different original common occurrence. -/ | joint
      (requested reported : Tagged left right request) (different : reported ≠ requested)

constructive_injectivity Failure

/-- Execute each original point or joint request at its retained input. -/
@[expose] def originalReply {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    Query left right request → Reply left right request budget equivalent leftCoherent rightCoherent
  | .inl question => .inl (Independent.originalReply left right request question)
  | .inr child => .inr ⟨child, ⟨jointForReading budget equivalent leftCoherent rightCoherent child.2.val, rfl⟩⟩

/-- Display an original owner-specific point request inside the combined boundary. -/
@[expose] def pointHandler {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (question : Independent.Query left right) : Program (Query left right request)
      (Reply left right request budget equivalent leftCoherent rightCoherent)
      (Except (Failure left right request) (Independent.Reply left right request)) :=
  .request (.inl question) fun response => match response with
    | .inl point => .pure (.ok point)
    | .inr _ => .pure (.error (.operation (.inl question)))

/-- Observe one joint scheduler request using the returned common reading itself. -/
@[expose] def jointRequest {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (child : Tagged left right request) : Program (Query left right request)
      (Reply left right request budget equivalent leftCoherent rightCoherent)
      (Except (Failure left right request)
        (Selected left right request budget equivalent leftCoherent rightCoherent child)) :=
  .request (.inr child) fun response => match response with
    | .inl _ => .pure (.error (.operation (.inr child)))
    | .inr returned =>
        if same : returned.child = child then .pure (.ok (same ▸ returned.result))
        else .pure (.error (.joint child returned.child same))

/-- The joint result retains the exact common reading supplied to its scheduler. -/
theorem selected_reading {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (child : Tagged left right request)
    (result : Selected left right request budget equivalent leftCoherent rightCoherent child) :
    result.val.reading = child.2.val :=
  congrArg JointReading.reading result.property

/-- Original joint replies return the exact scheduler result for the displayed common reading. -/
theorem jointRequest_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (child : Tagged left right request) :
    ((jointRequest left right request budget equivalent leftCoherent rightCoherent child).protocol.run
      (originalReply left right request budget equivalent leftCoherent rightCoherent)).value =
        .ok ⟨jointForReading budget equivalent leftCoherent rightCoherent child.2.val, rfl⟩ := by
  change ((if same : child = child then
    (Program.pure (.ok (same ▸ (⟨jointForReading budget equivalent leftCoherent rightCoherent child.2.val, rfl⟩ :
      Selected left right request budget equivalent leftCoherent rightCoherent child))) :
      Program (Query left right request) (Reply left right request budget equivalent leftCoherent rightCoherent)
        (Except (Failure left right request)
          (Selected left right request budget equivalent leftCoherent rightCoherent child)))
    else Program.pure (.error (.joint child child same))).protocol.run
      (originalReply left right request budget equivalent leftCoherent rightCoherent)).value = _
  rw [dif_pos rfl]
  rfl

/-- Observe all original point requests before making any joint scheduler request. -/
@[expose] def pointProgram {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    Program (Query left right request) (Reply left right request budget equivalent leftCoherent rightCoherent)
      (Except (Failure left right request)
        (Basic.Execution (Independent.Query left right) (Independent.Reply left right request)
          (Except (Independent.Failure left right)
            (Independent.Batch left right request (Purelib.Data.List.indices (occurrences left right)))))) :=
  (Independent.batch left right request (Independent.pair left right request)
    (Purelib.Data.List.indices (occurrences left right))).substituteChecked
      (pointHandler left right request budget equivalent leftCoherent rightCoherent)

/-- Original point handlers retain the complete independent acquisition and its ordered point trace. -/
theorem pointProgram_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    ((pointProgram left right request budget equivalent leftCoherent rightCoherent).protocol.run
      (originalReply left right request budget equivalent leftCoherent rightCoherent)).value =
        .ok ((Independent.batch left right request (Independent.pair left right request)
          (Purelib.Data.List.indices (occurrences left right))).protocol.run
            (Independent.originalReply left right request)) := by
  unfold pointProgram
  apply Program.substituteChecked_value
  intro question
  rfl

/-- Ordered joint results certified against each supplied original common occurrence. -/
abbrev Batch {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (children : List (Tagged left right request)) :=
  {results : List (JointReading left right request budget) //
    results = children.map (fun child => jointForReading budget equivalent leftCoherent rightCoherent child.2.val)}

/-- Prepend the returned scheduler result to the already retained joint readings. -/
@[expose] def prepend {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (child : Tagged left right request) (remaining : List (Tagged left right request))
    (result : Selected left right request budget equivalent leftCoherent rightCoherent child)
    (tail : Batch left right request budget equivalent leftCoherent rightCoherent remaining) :
    Batch left right request budget equivalent leftCoherent rightCoherent (child :: remaining) :=
  ⟨result.val :: tail.val, congrArg₂ List.cons result.property tail.property⟩

/-- Request the joint scheduler for each returned common reading in order. -/
@[expose] def batch {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    (children : List (Tagged left right request)) →
      Program (Query left right request) (Reply left right request budget equivalent leftCoherent rightCoherent)
        (Except (Failure left right request)
          (Batch left right request budget equivalent leftCoherent rightCoherent children))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | child :: remaining =>
      (jointRequest left right request budget equivalent leftCoherent rightCoherent child).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok joint =>
            (batch left right request budget equivalent leftCoherent rightCoherent remaining).map fun after =>
              after.map (prepend left right request budget equivalent leftCoherent rightCoherent child remaining joint)

/-- Original joint replies return the scheduler results for all supplied readings in order. -/
theorem batch_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    ∀ children : List (Tagged left right request),
      ((batch left right request budget equivalent leftCoherent rightCoherent children).protocol.run
        (originalReply left right request budget equivalent leftCoherent rightCoherent)).value =
          .ok ⟨children.map (fun child => jointForReading budget equivalent leftCoherent rightCoherent child.2.val),
            rfl⟩
  | [] => rfl
  | child :: remaining => by
      change (((jointRequest left right request budget equivalent leftCoherent rightCoherent child).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok joint =>
            (batch left right request budget equivalent leftCoherent rightCoherent remaining).map fun after =>
              after.map (prepend left right request budget equivalent leftCoherent rightCoherent child remaining
                joint)).protocol.run
              (originalReply left right request budget equivalent leftCoherent rightCoherent)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, jointRequest_original]
      rw [Program.map_execution, Protocol.map_run_value,
        batch_original left right request budget equivalent leftCoherent rightCoherent remaining]
      rfl

/-- Assemble the returned joint scheduler results against the same returned common refinement. -/
@[expose] def assembleJoint {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (points : Independent.Batch left right request (Purelib.Data.List.indices (occurrences left right)))
    (joint : Batch left right request budget equivalent leftCoherent rightCoherent
      (tag left right request (Purelib.Data.List.indices (occurrences left right)) points)) :
    JointReadings (Independent.assemble left right request points) budget := by
  have readingEq : joint.val.map JointReading.reading = (Independent.assemble left right request points).readings := by
    rw [joint.property, Purelib.Data.List.Map.map_map]
    change (tag left right request (Purelib.Data.List.indices (occurrences left right)) points).map
      (fun child => child.2.val) = points.val
    exact tag_readings left right request _ points
  exact ⟨joint.val, readingEq⟩

/-- The returned joint results are the original scheduler applied to the same retained common readings. -/
theorem assembleJoint_eq {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (points : Independent.Batch left right request (Purelib.Data.List.indices (occurrences left right)))
    (joint : Batch left right request budget equivalent leftCoherent rightCoherent
      (tag left right request (Purelib.Data.List.indices (occurrences left right)) points)) :
    assembleJoint left right request budget equivalent leftCoherent rightCoherent points joint =
      requestJointReadings (Independent.assemble left right request points) budget equivalent leftCoherent
        rightCoherent := by
  have same : joint.val = (requestJointReadings (Independent.assemble left right request points)
      budget equivalent leftCoherent rightCoherent).readings := by
    rw [joint.property]
    change (tag left right request (Purelib.Data.List.indices (occurrences left right)) points).map
      ((jointForReading budget equivalent leftCoherent rightCoherent) ∘ (fun child => child.2.val)) =
        points.val.map (jointForReading budget equivalent leftCoherent rightCoherent)
    rw [← Purelib.Data.List.Map.map_map, tag_readings]
  cases joint with
  | mk values property =>
    cases same
    rfl

/-- The actual common refinement and its associated returned joint scheduler results. -/
abbrev Result {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest) :=
  Σ common : CommonReadings left right request, JointReadings common budget

/-- Retain the actual returned common and joint readings together. -/
@[expose] def assembleComparison {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (points : Independent.Batch left right request (Purelib.Data.List.indices (occurrences left right)))
    (joint : Batch left right request budget equivalent leftCoherent rightCoherent
      (tag left right request (Purelib.Data.List.indices (occurrences left right)) points)) :
    Result left right request budget :=
  ⟨Independent.assemble left right request points,
    assembleJoint left right request budget equivalent leftCoherent rightCoherent points joint⟩

/-- The returned comparison is the original common refinement and its joint scheduler results. -/
theorem assembleComparison_eq {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (points : Independent.Batch left right request (Purelib.Data.List.indices (occurrences left right)))
    (joint : Batch left right request budget equivalent leftCoherent rightCoherent
      (tag left right request (Purelib.Data.List.indices (occurrences left right)) points)) :
    assembleComparison left right request budget equivalent leftCoherent rightCoherent points joint =
      ⟨commonReadings left right request,
        requestJointReadings (commonReadings left right request) budget equivalent leftCoherent rightCoherent⟩ := by
  unfold assembleComparison
  rw [assembleJoint_eq, Independent.assemble_eq]

/-- Acquire both original source readings, then request joint admission at those same returned readings. -/
@[expose] def computation {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    Program (Query left right request) (Reply left right request budget equivalent leftCoherent rightCoherent)
      (Except (Failure left right request) (Result left right request budget)) :=
  (pointProgram left right request budget equivalent leftCoherent rightCoherent).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok execution =>
        match execution.value with
        | .error invalid => .pure (.error (.point invalid))
        | .ok points =>
            (batch left right request budget equivalent leftCoherent rightCoherent
              (tag left right request (Purelib.Data.List.indices (occurrences left right)) points)).map fun result =>
                result.map (assembleComparison left right request budget equivalent leftCoherent rightCoherent points)

/-- Original point and joint replies return the complete original common and joint comparison. -/
theorem computation_original {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    ((computation left right request budget equivalent leftCoherent rightCoherent).protocol.run
      (originalReply left right request budget equivalent leftCoherent rightCoherent)).value =
      .ok ⟨commonReadings left right request,
        requestJointReadings (commonReadings left right request) budget equivalent leftCoherent rightCoherent⟩ := by
  unfold computation
  rw [Program.bind_execution, Protocol.bind_run_value, pointProgram_original]
  dsimp only
  rw [Independent.batch_original left right request (Independent.pair left right request)
    (Independent.originalReply left right request) (Independent.pair_original left right request)]
  rw [Program.map_execution, Protocol.map_run_value, batch_original]
  apply congrArg Except.ok
  exact assembleComparison_eq left right request budget equivalent leftCoherent rightCoherent _ _

/-- Exact replay returns the complete original comparison without repeating point or joint requests. -/
theorem computation_replay {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    let program := computation left right request budget equivalent leftCoherent rightCoherent
    let oracle := originalReply left right request budget equivalent leftCoherent rightCoherent
    program.protocol.replayExact (program.protocol.run oracle).trace =
      .ok (.ok ⟨commonReadings left right request,
        requestJointReadings (commonReadings left right request) budget equivalent leftCoherent rightCoherent⟩) := by
  let program := computation left right request budget equivalent leftCoherent rightCoherent
  let oracle := originalReply left right request budget equivalent leftCoherent rightCoherent
  change program.protocol.replayExact (program.protocol.run oracle).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Replies outside the executed combined trace preserve its complete comparison and ordered requests. -/
theorem payload_erasure {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource) (request budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) {Payload : Type} (payload : Payload)
    (outside : Payload → Query left right request →
      Reply left right request budget equivalent leftCoherent rightCoherent) :
    let program := computation left right request budget equivalent leftCoherent rightCoherent
    let oracle := originalReply left right request budget equivalent leftCoherent rightCoherent
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run oracle).trace (outside payload)) =
      program.protocol.run oracle :=
  (computation left right request budget equivalent leftCoherent rightCoherent).protocol.annotation_erasure
    (originalReply left right request budget equivalent leftCoherent rightCoherent) payload outside

end Joint

end Purelib.Integration.NumericalFrontier.Common.Observation.Independent

end
