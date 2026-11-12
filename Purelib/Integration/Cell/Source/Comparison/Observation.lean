module
public import Purelib.Integration.Cell.Source.Comparison.Weights
public import Purelib.Computation.Query.Program
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing exact source comparisons

Two original source owners and their finite frontiers are fixed inputs. Each
common child reuses its actual parent point at a matching tag and otherwise
requests that owner's exact rational reading. Returned readings construct the
same indexed common refinement that pays for the integral-answer comparison.
-/

public section

namespace Purelib.Integration.SourceFrontier.Comparison.Observation

open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- A rational reading requested from one of two original source owners. -/
abbrev Query := Sum Fraction.Rational Fraction.Rational

/-- A reply belongs to one of the two original source owners. -/
abbrev Reply (leftSource rightSource : Fraction.Rational → Fraction.Rational) :=
  Sum (SourcePoint leftSource) (SourcePoint rightSource)

set_option genInjectivity false in
/-- An exact common-point request was answered by the wrong owner or with the wrong tag. -/
inductive Failure where
  /-- The response belongs to the other original source owner. -/ | owner (requested : Query)
  /-- The response's tag differs from the requested rational point. -/ | tag
      (requested : Query) (reported : Fraction.Rational) (different : reported ≠ requested.elim id id)

constructive_injectivity Failure

/-- Read the specified original source at an arbitrary rational tag. -/
@[expose] def originalPoint (source : Fraction.Rational → Fraction.Rational) (point : Fraction.Rational) :
    SourcePoint source :=
  SourcePoint.observe source ⟨point, point⟩ point le_rfl le_rfl

/-- The two original owners answer their own displayed requests. -/
@[expose] def originalReply (leftSource rightSource : Fraction.Rational → Fraction.Rational) :
    Query → Reply leftSource rightSource
  | .inl point => .inl (originalPoint leftSource point)
  | .inr point => .inr (originalPoint rightSource point)

/-- An exact reading certified as the original parent point's actual read operation. -/
abbrev Reading {source : Fraction.Rational → Fraction.Rational} (retained : SourcePoint source)
    (point : Fraction.Rational) := {value : Fraction.Rational // value = retained.readAt point}

/-- Read one original parent, using its saved value at its own tag and otherwise the displayed response. -/
@[expose] def readPoint {source : Fraction.Rational → Fraction.Rational} {R : Type}
    (retained : SourcePoint source) (point : Fraction.Rational) (question : Query)
    (questionPoint : question.elim id id = point) (decode : R → Option (SourcePoint source)) :
    Program Query R (Except Failure (Reading retained point)) :=
  match retained.savedReading point with
  | some reading => .pure (.ok ⟨reading.val, reading.property.trans (retained.readAt_eq point).symm⟩)
  | none =>
      .request question fun response =>
        match decode response with
        | none => .pure (.error (.owner question))
        | some reply =>
            if sameTag : reply.point = point then
              .pure (.ok ⟨reply.reading, (reply.reading_eq.trans (congrArg source sameTag)).trans
                (retained.readAt_eq point).symm⟩)
            else .pure (.error (.tag question reply.point (by rw [questionPoint]; exact sameTag)))

/-- With the original response, a parent lookup returns its actual exact reading. -/
theorem readPoint_original {source : Fraction.Rational → Fraction.Rational} {R : Type}
    (retained : SourcePoint source) (point : Fraction.Rational) (question : Query)
    (questionPoint : question.elim id id = point) (decode : R → Option (SourcePoint source))
    (oracle : Query → R) (response : decode (oracle question) = some (originalPoint source point)) :
    ((readPoint retained point question questionPoint decode).protocol.run oracle).value =
      .ok ⟨retained.readAt point, rfl⟩ := by
  unfold readPoint
  cases found : retained.savedReading point with
  | some reading =>
      apply congrArg Except.ok
      apply Subtype.ext
      exact reading.property.trans (retained.readAt_eq point).symm
  | none =>
      change ((match decode (oracle question) with
        | none => (Program.pure (.error (.owner question)) : Program Query R (Except Failure (Reading retained point)))
        | some reply => if sameTag : reply.point = point then
            .pure (.ok ⟨reply.reading, (reply.reading_eq.trans (congrArg source sameTag)).trans
              (retained.readAt_eq point).symm⟩)
          else .pure (.error (.tag question reply.point (by rw [questionPoint]; exact sameTag)))).protocol.run
            oracle).value = _
      rw [response]
      dsimp only
      have sameTag : (originalPoint source point).point = point := rfl
      rw [dif_pos sameTag]
      apply congrArg Except.ok
      apply Subtype.ext
      exact ((originalPoint source point).reading_eq.trans (congrArg source sameTag)).trans
        (retained.readAt_eq point).symm

/-- The returned reading pair belongs to the exact two original parent points. -/
@[expose] def readPair {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourcePoint leftSource) (right : SourcePoint rightSource) (point : Fraction.Rational) :
    Program Query (Reply leftSource rightSource) (Except Failure (ReadingPair left right point)) :=
  (readPoint left point (.inl point) rfl (fun response => match response with
    | .inl reply => some reply | .inr _ => none)).bind fun first =>
    match first with
    | .error invalid => .pure (.error invalid)
    | .ok leftReading =>
        (readPoint right point (.inr point) rfl (fun response => match response with
          | .inl _ => none | .inr reply => some reply)).map fun second =>
            second.map fun rightReading => ⟨⟨leftReading.val, rightReading.val⟩,
              leftReading.property, rightReading.property⟩

/-- Original-source execution returns the original pair of parent readings. -/
theorem readPair_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourcePoint leftSource) (right : SourcePoint rightSource) (point : Fraction.Rational) :
    ((readPair left right point).protocol.run (originalReply leftSource rightSource)).value =
      .ok (independentPair left right point) := by
  unfold readPair
  rw [Program.bind_execution, Protocol.bind_run_value, readPoint_original _ _ _ _ _ _ rfl]
  rw [Program.map_execution, Protocol.map_run_value, readPoint_original _ _ _ _ _ _ rfl]
  rfl

/-- A child occurrence in the original computed common refinement. -/
abbrev Entry {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :=
  {entry // entry ∈ refinement.entries}

/-- Each common child has the original partition's unit-interval validity. -/
theorem entryValid {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement) :
    entry.val.child.Valid := by
  have member : entry.val.child ∈ refinement.partition.intervals := by
    rw [← refinement.children_eq]
    exact (Purelib.Data.List.Map.mem_map).mpr ⟨entry.val, entry.property, rfl⟩
  exact refinement.partition.valid entry.val.child member

/-- The original common child reads the left endpoint of its exact indexed occurrence. -/
@[expose] def originalChild {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement) :
    CommonReading left right :=
  readCommon left right entry.val (entryValid refinement entry) entry.val.child.start
    ⟨le_rfl, (entryValid refinement entry).2.1.le⟩

/-- Assemble an actual common child from the returned pair of original-parent readings. -/
@[expose] def returnedChild {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement)
    (pair : ReadingPair (left.partitioned.cellAtOwner entry.val.leftOwner).val.item
      (right.partitioned.cellAtOwner entry.val.rightOwner).val.item entry.val.child.start) : CommonReading left right :=
  readCommonFromPair left right entry.val (entryValid refinement entry) entry.val.child.start
    ⟨le_rfl, (entryValid refinement entry).2.1.le⟩ pair

/-- The returned child is exactly the original common child, including both indexed owners. -/
theorem returnedChild_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement)
    (pair : ReadingPair (left.partitioned.cellAtOwner entry.val.leftOwner).val.item
      (right.partitioned.cellAtOwner entry.val.rightOwner).val.item entry.val.child.start) :
    returnedChild left right refinement entry pair = originalChild left right refinement entry := by
  unfold returnedChild originalChild readCommon readCommonWith
  rw [readingPair_eq pair]

/-- Ordered returned children certified against the exact original common occurrences. -/
abbrev Batch {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entries : List (Entry left right refinement)) :=
  {readings : List (CommonReading left right) // readings = entries.map (originalChild left right refinement)}

/-- Prepend the returned pair to the already returned common children. -/
@[expose] def prepend {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement)
    (remaining : List (Entry left right refinement))
    (pair : ReadingPair (left.partitioned.cellAtOwner entry.val.leftOwner).val.item
      (right.partitioned.cellAtOwner entry.val.rightOwner).val.item entry.val.child.start)
    (tail : Batch left right refinement remaining) : Batch left right refinement (entry :: remaining) :=
  ⟨returnedChild left right refinement entry pair :: tail.val,
    congrArg₂ List.cons (returnedChild_eq left right refinement entry pair) tail.property⟩

/-- Observe each common child in order, stopping at the first invalid owner or tag. -/
@[expose] def batch {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    (entries : List (Entry left right refinement)) → Program Query (Reply leftSource rightSource)
      (Except Failure (Batch left right refinement entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining =>
      (readPair (left.partitioned.cellAtOwner entry.val.leftOwner).val.item
        (right.partitioned.cellAtOwner entry.val.rightOwner).val.item entry.val.child.start).bind fun pair =>
        match pair with
        | .error invalid => .pure (.error invalid)
        | .ok pair => (batch left right refinement remaining).map fun after =>
            after.map (prepend left right refinement entry remaining pair)

/-- Original-source execution returns the original common children in their exact order. -/
theorem batch_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    ∀ entries : List (Entry left right refinement),
      ((batch left right refinement entries).protocol.run (originalReply leftSource rightSource)).value =
        .ok ⟨entries.map (originalChild left right refinement), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((readPair (left.partitioned.cellAtOwner entry.val.leftOwner).val.item
        (right.partitioned.cellAtOwner entry.val.rightOwner).val.item entry.val.child.start).bind fun pair =>
        match pair with
        | .error invalid => .pure (.error invalid)
        | .ok pair => (batch left right refinement remaining).map fun after =>
            after.map (prepend left right refinement entry remaining pair)).protocol.run
              (originalReply leftSource rightSource)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, readPair_original]
      rw [Program.map_execution, Protocol.map_run_value, batch_original left right refinement remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      change returnedChild left right refinement entry _ :: _ = _
      rw [returnedChild_eq]
      rfl

/-- Assemble the actual returned common refinement without re-reading either source. -/
@[expose] def assemble {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (returned : Batch left right (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach) : CommonReadings left right := by
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  have entries_eq : returned.val.map CommonReading.entry = refinement.entries := by
    rw [returned.property, Purelib.Data.List.Map.map_map]
    change refinement.entries.attach.map Subtype.val = refinement.entries
    exact Purelib.Data.List.attach_map_subtype_val _
  exact ⟨refinement, returned.val, entries_eq⟩

/-- The assembled returned children are the complete original common comparison. -/
theorem assemble_eq {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (returned : Batch left right (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach) :
    assemble left right returned = commonReadings left right := by
  refine CommonReadings.ext _ _ ?_ ?_
  · rfl
  · exact returned.property

/-- A returned common refinement certified as the original ordered comparison. -/
abbrev Certified {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :=
  {common : CommonReadings left right // common = commonReadings left right}

/-- Construct the original common refinement from the same returned source observations.

Each returned child is assembled once into the actual comparison. Its
certificate identifies that retained comparison with the original indexed
construction, without requesting either source again. -/
@[expose] def certifiedComputation {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    Program Query (Reply leftSource rightSource) (Except Failure (Certified left right)) :=
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  (batch left right refinement refinement.entries.attach).map fun returned =>
    returned.map fun children => ⟨assemble left right children, assemble_eq left right children⟩

/-- Original source replies return the complete certified common refinement. -/
theorem certified_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    ((certifiedComputation left right).protocol.run (originalReply leftSource rightSource)).value =
      .ok ⟨commonReadings left right, rfl⟩ := by
  unfold certifiedComputation
  rw [Program.map_execution, Protocol.map_run_value, batch_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assemble_eq left right _

/-- Exact replay retains the certified comparison without repeating either source request. -/
theorem certified_replay {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    (certifiedComputation left right).protocol.replayExact
      ((certifiedComputation left right).protocol.run (originalReply leftSource rightSource)).trace =
        .ok (.ok ⟨commonReadings left right, rfl⟩) := by
  rw [(certifiedComputation left right).protocol.replayExact_run, certified_original]

/-- Changes outside the certified comparison's actual trace preserve its complete execution. -/
theorem certified_payload_erasure {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply leftSource rightSource) :
    (certifiedComputation left right).protocol.run (Boundary.Trace.overlay
      ((certifiedComputation left right).protocol.run (originalReply leftSource rightSource)).trace (outside payload)) =
      (certifiedComputation left right).protocol.run (originalReply leftSource rightSource) :=
  (certifiedComputation left right).protocol.annotation_erasure (originalReply leftSource rightSource) payload outside

/-- The original source comparison driven by cached or returned owner-specific readings. -/
@[expose] def computation {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    Program Query (Reply leftSource rightSource) (Except Failure (CommonReadings left right)) :=
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  (batch left right refinement refinement.entries.attach).map fun returned => returned.map (assemble left right)

/-- The certified and plain views have the same result after projection and the same ordered trace.

The law covers every oracle, including replies rejected for a wrong owner or
tag. Both views consume the same original batch and assembly operations. -/
theorem certified_projection {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (oracle : Query → Reply leftSource rightSource) :
    let certified := (certifiedComputation left right).protocol.run oracle
    let plain := (computation left right).protocol.run oracle
    certified.value.map Subtype.val = plain.value ∧ certified.trace = plain.trace := by
  unfold certifiedComputation computation
  constructor
  · rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value]
    cases ((batch left right (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach).protocol.run oracle).value <;> rfl
  · rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace]

/-- Original-source execution returns the complete original common comparison. -/
theorem computation_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    ((computation left right).protocol.run (originalReply leftSource rightSource)).value =
      .ok (commonReadings left right) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, batch_original]
  apply congrArg Except.ok
  exact assemble_eq left right _

/-- Exact replay recovers the original comparison without repeating either displayed source request. -/
theorem computation_replay {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    (computation left right).protocol.replayExact
      ((computation left right).protocol.run (originalReply leftSource rightSource)).trace =
        .ok (.ok (commonReadings left right)) := by
  rw [(computation left right).protocol.replayExact_run, computation_original]

/-- Replies outside the actual comparison trace preserve its complete result and ordered trace. -/
theorem payload_erasure {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply leftSource rightSource) :
    (computation left right).protocol.run (Boundary.Trace.overlay
      ((computation left right).protocol.run (originalReply leftSource rightSource)).trace (outside payload)) =
      (computation left right).protocol.run (originalReply leftSource rightSource) :=
  (computation left right).protocol.annotation_erasure (originalReply leftSource rightSource) payload outside

/-- The actually returned common readings pay for the two retained integral answers. -/
theorem returned_answers_difference_le {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) (leftAnswer rightAnswer : Fraction.Rational)
    (leftInside : (integralBound left.cells).Contains leftAnswer)
    (rightInside : (integralBound right.cells).Contains rightAnswer) :
    Fraction.abs (leftAnswer - rightAnswer) ≤
      (integralBound left.cells).width + (integralBound right.cells).width + common.pointBudget :=
  common.answers_difference_le leftAnswer rightAnswer leftInside rightInside

end Purelib.Integration.SourceFrontier.Comparison.Observation

end
