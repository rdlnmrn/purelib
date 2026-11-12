module
public import Purelib.Integration.Cell.Numerical.Common
public import Purelib.Computation.Query.Program
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing cached numerical common refinements

The source, finite point bank, two frontiers and accuracy request are fixed.
Every common child uses one observation of its original point process on both
sides. A sufficient saved state makes no request; otherwise the returned point
retains the actual selected predecessor and supplies the common construction.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Common.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- A common-child interval whose left endpoint is the requested rational tag. -/
abbrev Query := {interval : Partition.Interval // interval.Valid}

/-- A point observation certified as the actual cache-selected request for one interval. -/
abbrev Selected {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (query : Query) :=
  {point : NumericalPoint.Observation source query.val query.val.start request //
    point = NumericalPoint.atStartCached source cached query.val query.property request}

set_option genInjectivity false in
/-- A returned point observation and its original requested interval. -/
structure Reply {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (request : AccuracyRequest) where
  /-- The valid original common-child interval for the returned observation. -/ query : Query
  /-- The actual selected numerical state, interval and saved predecessor. -/ point : Selected cached request query

constructive_injectivity Reply

set_option genInjectivity false in
/-- A numerical point reply for an interval other than the requested common child. -/
structure Invalid where
  /-- The requested common-child interval. -/ requested : Query
  /-- The returned common-child interval. -/ reported : Query
  /-- The returned interval differs from the requested interval. -/ different : reported ≠ requested

constructive_injectivity Invalid

/-- The original cache-selected point for each displayed common-child interval. -/
@[expose] def originalReply {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (query : Query) : Reply cached request :=
  ⟨query, ⟨NumericalPoint.atStartCached source cached query.val query.property request, rfl⟩⟩

/-- Reuse a sufficient saved state or request the original common-child point exactly once. -/
@[expose] def point {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (query : Query) :
    Program Query (Reply cached request) (Except Invalid (Selected cached request query)) :=
  match NumericalPoint.findSufficient cached query.val.start request with
  | some _ => .pure (.ok ⟨NumericalPoint.atStartCached source cached query.val query.property request, rfl⟩)
  | none => .request query fun reply =>
      if same : reply.query = query then .pure (.ok (same ▸ reply.point))
      else .pure (.error ⟨query, reply.query, same⟩)

/-- Original execution returns the exact point selected from the retained bank. -/
theorem point_original {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (query : Query) :
    ((point cached request query).protocol.run (originalReply cached request)).value =
      .ok ⟨NumericalPoint.atStartCached source cached query.val query.property request, rfl⟩ := by
  unfold point
  cases found : NumericalPoint.findSufficient cached query.val.start request with
  | some retained => rfl
  | none =>
      change (((if same : (originalReply cached request query).query = query then
        (Program.pure (.ok (same ▸ (originalReply cached request query).point)) :
          Program Query (Reply cached request) (Except Invalid (Selected cached request query)))
        else Program.pure (.error ⟨query, (originalReply cached request query).query, same⟩)).protocol).run
          (originalReply cached request)).value = _
      have same : (originalReply cached request query).query = query := rfl
      rewrite [dif_pos same]
      rfl

/-- A sufficient original state is reused with no displayed point request. -/
theorem point_hit_trace {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (request : AccuracyRequest) (query : Query)
    (retained : {point : NumericalPoint source // point.point = query.val.start ∧
      point.reading.width < request.tolerance})
    (found : NumericalPoint.findSufficient cached query.val.start request = some retained)
    (oracle : Query → Reply cached request) : ((point cached request query).protocol.run oracle).trace = [] := by
  unfold point
  rewrite [found]
  rfl

/-- An indexed common-child occurrence in the original retained refinement. -/
abbrev Entry {source : Fraction.Rational → BoundProcess} (left right : NumericalFrontier source)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :=
  {entry // entry ∈ refinement.entries}

/-- Every original common child is a valid unit interval. -/
theorem entryValid {source : Fraction.Rational → BoundProcess} {left right : NumericalFrontier source}
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement) :
    entry.val.child.Valid := by
  have member : entry.val.child ∈ refinement.partition.intervals := by
    rw [← refinement.children_eq]
    exact (Purelib.Data.List.Map.mem_map).mpr ⟨entry.val, entry.property, rfl⟩
  exact refinement.partition.valid entry.val.child member

/-- The requested child interval retains its original validity certificate. -/
@[expose] def entryQuery {source : Fraction.Rational → BoundProcess} {left right : NumericalFrontier source}
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement) :
    Query := ⟨entry.val.child, entryValid refinement entry⟩

/-- The original common child selects one saved or continued point for both original parent owners. -/
@[expose] def originalChild {source : Fraction.Rational → BoundProcess}
    (cached : List (NumericalPoint source)) (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement) :
    CommonReading left right request :=
  readCommonWith left right request entry.val (entryValid refinement entry) entry.val.child.start
    ⟨le_rfl, (entryValid refinement entry).2.1.le⟩
    (cachedPair cached entry.val.child (entryValid refinement entry) entry.val.child.start
      ⟨le_rfl, (entryValid refinement entry).2.1.le⟩ request)

/-- Construct both common-child views from the same returned numerical point observation. -/
@[expose] def returnedChild {source : Fraction.Rational → BoundProcess}
    (cached : List (NumericalPoint source)) (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement)
    (selected : Selected cached request (entryQuery refinement entry)) : CommonReading left right request :=
  readCommonFromPair left right request entry.val (entryValid refinement entry) entry.val.child.start
    ⟨le_rfl, (entryValid refinement entry).2.1.le⟩
    (pairFromObservation entry.val.child entry.val.child.start ⟨le_rfl, (entryValid refinement entry).2.1.le⟩
      request selected.val)

/-- Returned point data construct the exact original cached common child. -/
theorem returnedChild_eq {source : Fraction.Rational → BoundProcess}
    (cached : List (NumericalPoint source)) (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement)
    (selected : Selected cached request (entryQuery refinement entry)) :
    returnedChild cached left right request refinement entry selected =
      originalChild cached left right request refinement entry := by
  unfold returnedChild originalChild readCommonWith cachedPair
  rw [selected.property]
  rfl

/-- Ordered returned numerical children certified against their original indexed occurrences. -/
abbrev Batch {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition)
    (entries : List (Entry left right refinement)) :=
  {readings : List (CommonReading left right request) //
    readings = entries.map (originalChild cached left right request refinement)}

/-- Prepend an observed common child to the already returned ordered children. -/
@[expose] def prepend {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) (entry : Entry left right refinement)
    (remaining : List (Entry left right refinement)) (selected : Selected cached request (entryQuery refinement entry))
    (tail : Batch cached left right request refinement remaining) :
    Batch cached left right request refinement (entry :: remaining) :=
  ⟨returnedChild cached left right request refinement entry selected :: tail.val,
    congrArg₂ List.cons (returnedChild_eq cached left right request refinement entry selected) tail.property⟩

/-- Observe original common-child point states in order, stopping on the first wrong interval. -/
@[expose] def batch {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    (entries : List (Entry left right refinement)) → Program Query (Reply cached request)
      (Except Invalid (Batch cached left right request refinement entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining => (point cached request (entryQuery refinement entry)).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok selected => (batch cached left right request refinement remaining).map fun after =>
          after.map (prepend cached left right request refinement entry remaining selected)

/-- Original execution returns every actual common child in its original order. -/
theorem batch_original {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    (refinement : Unit.Common.CommonRefinement left.partition right.partition) :
    ∀ entries : List (Entry left right refinement),
      ((batch cached left right request refinement entries).protocol.run (originalReply cached request)).value =
        .ok ⟨entries.map (originalChild cached left right request refinement), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((point cached request (entryQuery refinement entry)).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok selected => (batch cached left right request refinement remaining).map fun after =>
            after.map (prepend cached left right request refinement entry remaining selected)).protocol.run
              (originalReply cached request)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, point_original]
      rw [Program.map_execution, Protocol.map_run_value, batch_original cached left right request refinement remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      change returnedChild cached left right request refinement entry _ :: _ = _
      rw [returnedChild_eq]
      rfl

/-- Assemble the original common refinement from its returned observations without another point request. -/
@[expose] def assemble {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    (returned : Batch cached left right request (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach) :
    CommonReadings left right request := by
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  have entries_eq : returned.val.map CommonReading.entry = refinement.entries := by
    rw [returned.property, Purelib.Data.List.Map.map_map]
    change refinement.entries.attach.map Subtype.val = refinement.entries
    exact Purelib.Data.List.attach_map_subtype_val _
  exact ⟨refinement, returned.val, entries_eq⟩

/-- Returned point data assemble into the original complete cached common refinement. -/
theorem assemble_eq {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    (returned : Batch cached left right request (Unit.Common.commonRefinement left.partition right.partition)
      (Unit.Common.commonRefinement left.partition right.partition).entries.attach) :
    assemble cached left right request returned = commonReadingsCached left right cached request := by
  refine CommonReadings.ext _ _ ?_ ?_
  · rfl
  · exact returned.property

/-- A returned common refinement certified as the exact original cached construction. -/
abbrev Certified {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest) :=
  {common : CommonReadings left right request // common = commonReadingsCached left right cached request}

/-- Construct the original certified common refinement from returned numerical observations. -/
@[expose] def certifiedComputation {source : Fraction.Rational → BoundProcess}
    (cached : List (NumericalPoint source)) (left right : NumericalFrontier source) (request : AccuracyRequest) :
    Program Query (Reply cached request) (Except Invalid (Certified cached left right request)) :=
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  (batch cached left right request refinement refinement.entries.attach).map fun returned =>
    returned.map fun children => ⟨assemble cached left right request children,
      assemble_eq cached left right request children⟩

/-- Original point replies return the complete certified cached common refinement. -/
theorem certified_original {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest) :
    ((certifiedComputation cached left right request).protocol.run (originalReply cached request)).value =
      .ok ⟨commonReadingsCached left right cached request, rfl⟩ := by
  unfold certifiedComputation
  rw [Program.map_execution, Protocol.map_run_value, batch_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact assemble_eq cached left right request _

/-- Observe the original cached common refinement, retaining its actual source-process states. -/
@[expose] def computation {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest) :
    Program Query (Reply cached request) (Except Invalid (CommonReadings left right request)) :=
  let refinement := Unit.Common.commonRefinement left.partition right.partition
  (batch cached left right request refinement refinement.entries.attach).map fun returned =>
    returned.map (assemble cached left right request)

/-- Original execution returns the complete actual cached common refinement. -/
theorem computation_original {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest) :
    ((computation cached left right request).protocol.run (originalReply cached request)).value =
      .ok (commonReadingsCached left right cached request) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, batch_original]
  apply congrArg Except.ok
  exact assemble_eq cached left right request _

/-- Exact replay returns the original common refinement without point-process requests. -/
theorem computation_replay {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest) :
    (computation cached left right request).protocol.replayExact
      ((computation cached left right request).protocol.run (originalReply cached request)).trace =
        .ok (.ok (commonReadingsCached left right cached request)) := by
  rw [(computation cached left right request).protocol.replayExact_run, computation_original]

/-- Replies outside the actual common-point trace preserve its complete returned result and ordered trace. -/
theorem payload_erasure {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (left right : NumericalFrontier source) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply cached request) :
    (computation cached left right request).protocol.run (Boundary.Trace.overlay
      ((computation cached left right request).protocol.run (originalReply cached request)).trace (outside payload)) =
      (computation cached left right request).protocol.run (originalReply cached request) :=
  (computation cached left right request).protocol.annotation_erasure (originalReply cached request) payload outside

end Purelib.Integration.NumericalFrontier.Common.Observation

end
