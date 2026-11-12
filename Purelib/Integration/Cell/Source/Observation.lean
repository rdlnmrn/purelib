module
public import Purelib.Integration.Cell.Source
public import Purelib.Computation.Query.Program
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing finite source-derived range frontiers

A finite partition, its range constructor and its source-validity law are
fixed inputs. Source requests expose only missing rational interval-start
readings. Returned points build the same ordered source-derived cells and
frontier as the original cached range construction.
-/

public section

namespace Purelib.Integration.SourceFrontier.Observation

open Purelib.Computation.Query
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- One exact occurrence of an interval in the original finite partition. -/
abbrev Entry (partition : Unit.Normalized) := {interval // interval ∈ partition.intervals}

/-- The source-admission law required by the original range-frontier constructor. -/
abbrev RangeValid (source : Fraction.Rational → Fraction.Rational) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) :=
  ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals) (point : Fraction.Rational),
    interval.start ≤ point → point ≤ interval.finish →
      (range (SourcePoint.atStart source interval (partition.valid interval member))).Contains (source point)

set_option genInjectivity false in
/-- A source reply at a tag other than the requested original interval start. -/
structure InvalidTag (partition : Unit.Normalized) where
  /-- The original interval occurrence whose start was requested. -/ entry : Entry partition
  /-- The rational tag actually returned. -/ reported : Fraction.Rational
  /-- The reported tag differs from the requested start. -/ different : reported ≠ entry.val.start

constructive_injectivity InvalidTag

/-- The original source observation at an actual partition occurrence. -/
@[expose] def originalReply (source : Fraction.Rational → Fraction.Rational) (partition : Unit.Normalized)
    (entry : Entry partition) : SourcePoint source :=
  SourcePoint.atStart source entry.val (partition.valid entry.val entry.property)

/-- Retain the supplied source reply at its matching original interval occurrence. -/
@[expose] def acquired {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (entry : Entry partition) (reply : SourcePoint source) (same : reply.point = entry.val.start) :
    SourcePoint source :=
  ⟨entry.val, entry.val.start, le_rfl, (partition.valid entry.val entry.property).2.1.le,
    reply.reading, reply.reading_eq.trans (congrArg source same)⟩

/-- A returned matching point is exactly the original cache-selected interval-start observation. -/
theorem acquired_eq_cached {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (cached : List (SourcePoint source)) (entry : Entry partition) (reply : SourcePoint source)
    (same : reply.point = entry.val.start) :
    acquired partition entry reply same =
      SourcePoint.atStartCached source cached entry.val (partition.valid entry.val entry.property) := by
  unfold acquired SourcePoint.atStartCached
  simp only [-eq_self, -iff_self, SourcePoint.readCached_eq, reply.reading_eq, same]
  rfl

/-- A returned exact point certified as the cache-selected original interval-start observation. -/
abbrev CachedPoint {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (cached : List (SourcePoint source)) (entry : Entry partition) :=
  {point : SourcePoint source // point = SourcePoint.atStartCached source cached entry.val
    (partition.valid entry.val entry.property)}

/-- Reuse a saved point at the original interval start or request its exact rational reading. -/
@[expose] def cachedPoint {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (cached : List (SourcePoint source)) (entry : Entry partition) :
    Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (CachedPoint partition cached entry)) :=
  match SourcePoint.findCached cached entry.val.start with
  | some retained => .pure (.ok ⟨acquired partition entry retained.val retained.property,
      acquired_eq_cached partition cached entry retained.val retained.property⟩)
  | none => .request entry fun reply =>
      if same : reply.point = entry.val.start then .pure (.ok ⟨acquired partition entry reply same,
        acquired_eq_cached partition cached entry reply same⟩)
      else .pure (.error ⟨entry, reply.point, same⟩)

/-- The original source returns the exact cache-selected point for one original occurrence. -/
theorem cachedPoint_original {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (cached : List (SourcePoint source)) (entry : Entry partition) :
    ((cachedPoint partition cached entry).protocol.run (originalReply source partition)).value =
      .ok ⟨SourcePoint.atStartCached source cached entry.val (partition.valid entry.val entry.property), rfl⟩ := by
  unfold cachedPoint
  cases found : SourcePoint.findCached cached entry.val.start with
  | some retained =>
      apply congrArg Except.ok
      apply Subtype.ext
      exact acquired_eq_cached partition cached entry retained.val retained.property
  | none =>
      change (((if same : (originalReply source partition entry).point = entry.val.start then
        (Program.pure (.ok ⟨acquired partition entry (originalReply source partition entry) same,
          acquired_eq_cached partition cached entry (originalReply source partition entry) same⟩) :
          Program (Entry partition) (SourcePoint source)
            (Except (InvalidTag partition) (CachedPoint partition cached entry)))
        else Program.pure (.error ⟨entry, (originalReply source partition entry).point, same⟩)).protocol).run
          (originalReply source partition)).value = _
      have same : (originalReply source partition entry).point = entry.val.start := rfl
      rw [dif_pos same]
      apply congrArg Except.ok
      apply Subtype.ext
      exact acquired_eq_cached partition cached entry (originalReply source partition entry) same

/-- Build the original interval's source-derived range from the same returned exact point. -/
@[expose] def returnedCell {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (entry : Entry partition) (point : SourcePoint source) :
    IntegrationCell (SourcePoint source) :=
  let bound := range point
  { item := point
    weight := entry.val.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos (partition.valid entry.val entry.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- Ordered returned cells certified against the original cache-selected range cells. -/
abbrev Cells {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (cached : List (SourcePoint source))
    (entries : List (Entry partition)) :=
  {cells : List (IntegrationCell (SourcePoint source)) //
    cells = entries.map (rangeCellCached source cached partition range)}

/-- Prepend one returned point cell to the already returned certified cells. -/
@[expose] def prepend {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (cached : List (SourcePoint source))
    (entry : Entry partition) (remaining : List (Entry partition)) (point : CachedPoint partition cached entry)
    (tail : Cells partition range cached remaining) : Cells partition range cached (entry :: remaining) := by
  have same : returnedCell partition range entry point.val = rangeCellCached source cached partition range entry := by
    rw [point.property]
    rfl
  exact ⟨returnedCell partition range entry point.val :: tail.val, congrArg₂ List.cons same tail.property⟩

/-- Observe the ordered original partition occurrences, stopping at the first wrong source tag. -/
@[expose] def cells {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (cached : List (SourcePoint source)) :
    (entries : List (Entry partition)) → Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (Cells partition range cached entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining => (cachedPoint partition cached entry).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok point => (cells partition range cached remaining).map fun after =>
          after.map (prepend partition range cached entry remaining point)

/-- Original execution returns every original cache-selected range cell in order. -/
theorem cells_original {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (cached : List (SourcePoint source)) :
    ∀ entries : List (Entry partition),
      ((cells partition range cached entries).protocol.run (originalReply source partition)).value =
        .ok ⟨entries.map (rangeCellCached source cached partition range), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((cachedPoint partition cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (cells partition range cached remaining).map fun after =>
            after.map (prepend partition range cached entry remaining point)).protocol.run
              (originalReply source partition)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, cachedPoint_original]
      rw [Program.map_execution, Protocol.map_run_value, cells_original partition range cached remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      rfl

/-- Build a complete source frontier directly from its returned, certified original cells. -/
@[expose] def frontierFromCells {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) (returned : Cells partition range cached partition.intervals.attach) :
    SourceFrontier source := by
  let original := ofRangesCached source cached partition range valid
  have cells_eq : returned.val = original.cells := returned.property
  exact
    { partition := partition
      cells := returned.val
      domains_eq := (congrArg (List.map (fun cell : IntegrationCell (SourcePoint source) => cell.item.interval))
        cells_eq).trans original.domains_eq
      weight_eq := by
        intro cell member
        exact original.weight_eq cell (cells_eq ▸ member)
      source_range := by
        intro cell member point lower upper
        exact original.source_range cell (cells_eq ▸ member) point lower upper }

/-- Returned cells assemble into the exact original cache-aware source frontier. -/
theorem frontierFromCells_eq {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) (returned : Cells partition range cached partition.intervals.attach) :
    frontierFromCells partition range valid cached returned = ofRangesCached source cached partition range valid :=
  SourceFrontier.ext _ _ rfl returned.property

/-- A returned source frontier certified as the original cache-aware range construction. -/
abbrev CertifiedFrontier {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) :=
  {frontier : SourceFrontier source // frontier = ofRangesCached source cached partition range valid}

/-- Observe the complete original cache-aware source-derived range frontier. -/
@[expose] def computation {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) : Program (Entry partition) (SourcePoint source)
      (Except (InvalidTag partition) (CertifiedFrontier partition range valid cached)) :=
  (cells partition range cached partition.intervals.attach).map fun returned =>
    returned.map fun result => ⟨frontierFromCells partition range valid cached result,
      frontierFromCells_eq partition range valid cached result⟩

/-- Original-source execution returns the complete original cache-aware range frontier. -/
theorem computation_original {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) :
    ((computation partition range valid cached).protocol.run (originalReply source partition)).value =
      .ok ⟨ofRangesCached source cached partition range valid, rfl⟩ := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, cells_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact frontierFromCells_eq partition range valid cached _

/-- Exact replay recovers the complete original range frontier without repeating source requests. -/
theorem computation_replay {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) :
    (computation partition range valid cached).protocol.replayExact
      ((computation partition range valid cached).protocol.run (originalReply source partition)).trace =
        .ok (.ok ⟨ofRangesCached source cached partition range valid, rfl⟩) := by
  rw [(computation partition range valid cached).protocol.replayExact_run, computation_original]

/-- Replies outside the displayed range-frontier trace preserve its complete result and ordered trace. -/
theorem payload_erasure {source : Fraction.Rational → Fraction.Rational} (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval) (valid : RangeValid source partition range)
    (cached : List (SourcePoint source)) {Payload : Type} (payload : Payload)
    (outside : Payload → Entry partition → SourcePoint source) :
    (computation partition range valid cached).protocol.run (Boundary.Trace.overlay
      ((computation partition range valid cached).protocol.run (originalReply source partition)).trace
      (outside payload)) =
      (computation partition range valid cached).protocol.run (originalReply source partition) :=
  (computation partition range valid cached).protocol.annotation_erasure
    (originalReply source partition) payload outside

end Purelib.Integration.SourceFrontier.Observation

end
