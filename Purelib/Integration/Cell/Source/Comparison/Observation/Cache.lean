module

public import Purelib.Integration.Cell.Source.Comparison.Observation

/-!
# Reusing exact common-point observations

The original comparison's queries are answered from the supplied banks when
their source owner and rational tag match. Other questions retain the original
checked source boundary. The original common-refinement program chooses its
own parent occurrences and consumes each returned reading.
-/

public section

namespace Purelib.Integration.SourceFrontier.Comparison.Observation.Cache

open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Select the actual cached source point at a tag, or the original source observation on a miss. -/
@[expose] def answerPoint (source : Fraction.Rational → Fraction.Rational)
    (bank : List (SourcePoint source)) (point : Fraction.Rational) : SourcePoint source :=
  match SourcePoint.findCached bank point with
  | some found => found.val
  | none => originalPoint source point

/-- The selected cached or original source point retains the requested rational tag. -/
theorem answerPoint_tag (source : Fraction.Rational → Fraction.Rational)
    (bank : List (SourcePoint source)) (point : Fraction.Rational) :
    (answerPoint source bank point).point = point := by
  unfold answerPoint
  cases SourcePoint.findCached bank point with
  | none => rfl
  | some found => exact found.property

/-- Answer each original owner from its own retained bank or its original source. -/
@[expose] def answer {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource)) :
    Query → Reply leftSource rightSource
  | .inl point => .inl (answerPoint leftSource leftBank point)
  | .inr point => .inr (answerPoint rightSource rightBank point)

/-- Reuse a matching original source point; otherwise display the unchanged original question. -/
@[expose] def handler {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (question : Query) : Program Query (Reply leftSource rightSource) (Except Empty (Reply leftSource rightSource)) :=
  match question with
  | .inl point =>
      match SourcePoint.findCached leftBank point with
      | some found => .pure (.ok (.inl found.val))
      | none => .request question fun reply => .pure (.ok reply)
  | .inr point =>
      match SourcePoint.findCached rightBank point with
      | some found => .pure (.ok (.inr found.val))
      | none => .request question fun reply => .pure (.ok reply)

/-- An original source answers a cache-aware question with the selected actual source point. -/
theorem handler_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource)) (question : Query) :
    ((handler leftBank rightBank question).protocol.run (originalReply leftSource rightSource)).value =
      .ok (answer leftBank rightBank question) := by
  cases question with
  | inl point =>
      unfold handler answer answerPoint
      dsimp only
      cases SourcePoint.findCached leftBank point <;> rfl
  | inr point =>
      unfold handler answer answerPoint
      dsimp only
      cases SourcePoint.findCached rightBank point <;> rfl

/-- A cached left point prevents a displayed query for its exact original tag. -/
theorem handler_left_hit {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (point : Fraction.Rational) (cached : {entry : SourcePoint leftSource // entry.point = point})
    (found : SourcePoint.findCached leftBank point = some cached) :
    handler leftBank rightBank (.inl point) = .pure (.ok (.inl cached.val)) := by
  unfold handler
  dsimp only
  rw [found]

/-- A cached right point prevents a displayed query for its exact original tag. -/
theorem handler_right_hit {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (point : Fraction.Rational) (cached : {entry : SourcePoint rightSource // entry.point = point})
    (found : SourcePoint.findCached rightBank point = some cached) :
    handler leftBank rightBank (.inr point) = .pure (.ok (.inr cached.val)) := by
  unfold handler
  dsimp only
  rw [found]

/-- The original parent accepts any same-owner reply at the requested rational tag. -/
theorem readPoint_answer {source : Fraction.Rational → Fraction.Rational} {R : Type}
    (retained : SourcePoint source) (point : Fraction.Rational) (question : Query)
    (questionPoint : question.elim id id = point) (decode : R → Option (SourcePoint source))
    (oracle : Query → R) (reply : SourcePoint source) (response : decode (oracle question) = some reply)
    (sameTag : reply.point = point) :
    ((readPoint retained point question questionPoint decode).protocol.run oracle).value =
      .ok ⟨retained.readAt point, rfl⟩ := by
  unfold readPoint
  cases retained.savedReading point with
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
      rw [dif_pos sameTag]
      apply congrArg Except.ok
      apply Subtype.ext
      exact (reply.reading_eq.trans (congrArg source sameTag)).trans (retained.readAt_eq point).symm

/-- Cached or original owner-specific replies recover the exact original pair of readings. -/
theorem readPair_answer {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourcePoint leftSource) (right : SourcePoint rightSource) (point : Fraction.Rational) :
    ((readPair left right point).protocol.run (answer leftBank rightBank)).value =
      .ok (independentPair left right point) := by
  unfold readPair
  rw [Program.bind_execution, Protocol.bind_run_value]
  rw [readPoint_answer _ _ _ _ _ _ (answerPoint leftSource leftBank point) rfl
    (answerPoint_tag leftSource leftBank point)]
  rw [Program.map_execution, Protocol.map_run_value]
  rw [readPoint_answer _ _ _ _ _ _ (answerPoint rightSource rightBank point) rfl
    (answerPoint_tag rightSource rightBank point)]
  rfl

/-- Cached replies preserve the exact ordered children of the original common refinement. -/
theorem batch_answer {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    ∀ entries : List (Entry left right refinement),
      ((batch left right refinement entries).protocol.run (answer leftBank rightBank)).value =
        .ok ⟨entries.map (originalChild left right refinement), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((readPair (left.partitioned.cellAtOwner entry.val.leftOwner).val.item
        (right.partitioned.cellAtOwner entry.val.rightOwner).val.item entry.val.child.start).bind fun pair =>
        match pair with
        | .error invalid => .pure (.error invalid)
        | .ok pair => (batch left right refinement remaining).map fun after =>
            after.map (prepend left right refinement entry remaining pair)).protocol.run
              (answer leftBank rightBank)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, readPair_answer]
      rw [Program.map_execution, Protocol.map_run_value,
        batch_answer leftBank rightBank left right refinement remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      change returnedChild left right refinement entry _ :: _ = _
      rw [returnedChild_eq]
      rfl

/-- Cached replies retain the complete original certified common comparison. -/
theorem certified_answer {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    ((certifiedComputation left right).protocol.run (answer leftBank rightBank)).value =
      .ok ⟨commonReadings left right, rfl⟩ := by
  unfold certifiedComputation
  rw [Program.map_execution, Protocol.map_run_value, batch_answer]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assemble_eq left right _

/-- Construct the original comparison from both saved point banks and actual cache-miss replies.

The original comparison program chooses its indexed common children and
consumes each returned scalar. A matching source point is returned directly;
a wrong owner or tag on a cache miss retains the original typed failure. -/
@[expose] def computation {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    Program Query (Reply leftSource rightSource) (Except Failure (Certified left right)) :=
  ((certifiedComputation left right).substituteChecked (handler leftBank rightBank)).map fun returned =>
    match returned with
    | .error impossible => nomatch impossible
    | .ok execution => execution.value

/-- Original source execution returns the original certified comparison using the saved banks. -/
theorem computation_original {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    ((computation leftBank rightBank left right).protocol.run (originalReply leftSource rightSource)).value =
      .ok ⟨commonReadings left right, rfl⟩ := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value (handler leftBank rightBank) (certifiedComputation left right)
    (originalReply leftSource rightSource) (answer leftBank rightBank) (handler_original leftBank rightBank)]
  dsimp only
  exact certified_answer leftBank rightBank left right

/-- Exact replay returns the original common comparison without repeating its source calls. -/
theorem computation_replay {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource) :
    (computation leftBank rightBank left right).protocol.replayExact
      ((computation leftBank rightBank left right).protocol.run (originalReply leftSource rightSource)).trace =
        .ok (.ok ⟨commonReadings left right, rfl⟩) := by
  rw [(computation leftBank rightBank left right).protocol.replayExact_run, computation_original]

/-- Replies outside the actual cache-miss trace preserve the complete comparison and ordered trace. -/
theorem payload_erasure {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    (leftBank : List (SourcePoint leftSource)) (rightBank : List (SourcePoint rightSource))
    (left : SourceFrontier leftSource) (right : SourceFrontier rightSource)
    {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply leftSource rightSource) :
    (computation leftBank rightBank left right).protocol.run (Boundary.Trace.overlay
      ((computation leftBank rightBank left right).protocol.run (originalReply leftSource rightSource)).trace
      (outside payload)) =
        (computation leftBank rightBank left right).protocol.run (originalReply leftSource rightSource) :=
  (computation leftBank rightBank left right).protocol.annotation_erasure (originalReply leftSource rightSource)
    payload outside

end Purelib.Integration.SourceFrontier.Comparison.Observation.Cache

end
