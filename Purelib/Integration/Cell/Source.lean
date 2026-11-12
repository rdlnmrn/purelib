module
public import Purelib.Integration.Cell.Basic
public import Purelib.Integration.Partition.Length
public import Purelib.Data.List.Attach
public import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Rational source-linked integration frontiers

Each retained cell carries a rational tag and its actual source reading. Its
range encloses the source at every rational point in the closed cell, and its
weight is the exact signed endpoint difference. The original unit partition
and all cell occurrences remain available in their original order.
-/

public section

namespace Purelib.Integration

open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- A rational tag and its exact reading in the retained source interval.

The reading is the original source applied to the retained point. Both
endpoints are included, including a point coinciding with a partition cut. -/
structure SourcePoint (source : Fraction.Rational → Fraction.Rational) where
  /-- The exact retained rational domain interval. -/ interval : Partition.Interval
  /-- The retained rational query point. -/ point : Fraction.Rational
  /-- The point is at or above the interval's starting endpoint. -/ start_le : interval.start ≤ point
  /-- The point is at or below the interval's finishing endpoint. -/ point_le_finish : point ≤ interval.finish
  /-- The cached exact source reading at the retained point. -/ reading : Fraction.Rational
  /-- The cached reading is the actual source output at the retained point. -/ reading_eq : reading = source point

constructive_injectivity SourcePoint

namespace SourcePoint

/-- Read the original exact source once at a supplied rational tag in its retained interval. -/
@[expose] def observe (source : Fraction.Rational → Fraction.Rational)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish) : SourcePoint source :=
  ⟨interval, point, start_le, point_le_finish, source point, rfl⟩

/-- Read an exact source at the start of a valid retained unit interval. -/
@[expose] def atStart (source : Fraction.Rational → Fraction.Rational)
    (interval : Partition.Interval) (valid : interval.Valid) : SourcePoint source :=
  observe source interval interval.start le_rfl valid.2.1.le

/-- Find the retained exact reading when the requested rational tag is the original tag. -/
@[expose] def savedReading {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (point : Fraction.Rational) :
    Option {reading : Fraction.Rational // reading = source point} :=
  if same : point = retained.point then
    some ⟨retained.reading, retained.reading_eq.trans (congrArg source same.symm)⟩ else none

/-- Read a rational point, reusing the retained exact reading when it is the original tag. -/
@[expose] def readAt {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (point : Fraction.Rational) : Fraction.Rational :=
  match retained.savedReading point with
  | some reading => reading.val
  | none => source point

/-- Reading the original tag uses the exact cached reading. -/
theorem readAt_point {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) : retained.readAt retained.point = retained.reading := by
  unfold readAt savedReading
  rw [dif_pos rfl]

/-- A cached or fresh read is the original source's exact value at the requested point. -/
theorem readAt_eq {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (point : Fraction.Rational) : retained.readAt point = source point := by
  unfold readAt
  cases retained.savedReading point with
  | some reading => exact reading.property
  | none => rfl

/-- Find the first retained observation at the supplied rational tag. -/
@[expose] def findCached {source : Fraction.Rational → Fraction.Rational} :
    List (SourcePoint source) → (point : Fraction.Rational) →
      Option {retained : SourcePoint source // retained.point = point}
  | [], _ => none
  | retained :: remaining, point =>
      if same : point = retained.point then some ⟨retained, same.symm⟩ else findCached remaining point

/-- A matching first observation is the actual cache lookup result. -/
theorem findCached_head {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (remaining : List (SourcePoint source)) :
    findCached (retained :: remaining) retained.point = some ⟨retained, rfl⟩ := by
  change (if same : retained.point = retained.point then some ⟨retained, same.symm⟩
    else findCached remaining retained.point) = _
  rw [dif_pos rfl]

/-- A different first tag is skipped by the actual cache lookup. -/
theorem findCached_cons_ne {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (remaining : List (SourcePoint source)) (point : Fraction.Rational)
    (different : point ≠ retained.point) :
    findCached (retained :: remaining) point = findCached remaining point := by
  change (if same : point = retained.point then some ⟨retained, same.symm⟩ else findCached remaining point) = _
  rw [dif_neg different]

/-- Read a rational point from the first matching retained observation, or query its original source. -/
@[expose] def readCached (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (point : Fraction.Rational) : Fraction.Rational :=
  match findCached cached point with
  | some retained => retained.val.reading
  | none => source point

/-- A matching first observation supplies its exact saved reading without calling the source. -/
theorem readCached_head {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (remaining : List (SourcePoint source)) :
    readCached source (retained :: remaining) retained.point = retained.reading := by
  unfold readCached
  rewrite [findCached_head]
  rfl

/-- A different first tag is skipped while retaining the rest of the observation bank. -/
theorem readCached_cons_ne {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (remaining : List (SourcePoint source)) (point : Fraction.Rational)
    (different : point ≠ retained.point) :
    readCached source (retained :: remaining) point = readCached source remaining point := by
  unfold readCached
  rw [findCached_cons_ne retained remaining point different]

/-- Every cached or fresh read has the original source's exact value at its tag. -/
theorem readCached_eq (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (point : Fraction.Rational) :
    readCached source cached point = source point := by
  unfold readCached
  cases findCached cached point with
  | none => rfl
  | some retained => exact retained.val.reading_eq.trans (congrArg source retained.property)

/-- Construct a start-tagged point using the first matching saved reading when available. -/
@[expose] def atStartCached (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (interval : Partition.Interval)
    (valid : interval.Valid) : SourcePoint source :=
  ⟨interval, interval.start, le_rfl, valid.2.1.le, readCached source cached interval.start,
    readCached_eq source cached interval.start⟩

/-- A cached observation at the new interval start supplies that same saved reading. -/
theorem atStartCached_reading_head {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (remaining : List (SourcePoint source))
    (interval : Partition.Interval) (valid : interval.Valid) (same : interval.start = retained.point) :
    (atStartCached source (retained :: remaining) interval valid).reading = retained.reading := by
  change readCached source (retained :: remaining) interval.start = retained.reading
  rw [same, readCached_head]

/-- Cached start-tag construction has the same point and exact reading as a fresh source observation. -/
theorem atStartCached_eq (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (interval : Partition.Interval) (valid : interval.Valid) :
    atStartCached source cached interval valid = atStart source interval valid := by
  unfold atStartCached atStart observe
  simp only [-eq_self, -iff_self, readCached_eq]
  rfl

/-- Retag a retained source reading on another displayed interval.

The new tag is checked against its own interval. The original reading is
reused when the tag is unchanged; otherwise the same source reads that point. -/
@[expose] def retag {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish) : SourcePoint source :=
  ⟨interval, point, start_le, point_le_finish, retained.readAt point, retained.readAt_eq point⟩

/-- Retagging at the original point retains the original cached reading. -/
theorem retag_reading_at_point {source : Fraction.Rational → Fraction.Rational}
    (retained : SourcePoint source) (interval : Partition.Interval)
    (start_le : interval.start ≤ retained.point) (point_le_finish : retained.point ≤ interval.finish) :
    (retained.retag interval retained.point start_le point_le_finish).reading = retained.reading :=
  retained.readAt_point

end SourcePoint

namespace IntegrationCell.Source

/-- A tagged cell has its actual domain length and encloses its source at every rational point of that domain. -/
@[expose] def Admitted {source : Fraction.Rational → Fraction.Rational}
    (cell : IntegrationCell (SourcePoint source)) : Prop :=
  cell.weight = cell.item.interval.signedLength ∧
    ∀ point, cell.item.interval.start ≤ point → point ≤ cell.item.interval.finish →
      cell.lower ≤ source point ∧ source point ≤ cell.upper

end IntegrationCell.Source

set_option genInjectivity false in
/-- A source-admitted, tagged enclosure over an original normalized unit partition.

The ordered cells read back to the partition's exact cached intervals. Each
cell retains its own tag, source reading and exact length, and its range is
certified for every rational point of that closed interval. -/
structure SourceFrontier (source : Fraction.Rational → Fraction.Rational) where
  /-- The original normalized unit partition. -/ partition : Unit.Normalized
  /-- The ordered tagged integration cells and their retained rational bounds. -/ cells :
    List (IntegrationCell (SourcePoint source))
  /-- Reading the cell domains returns the original partition interval list. -/ domains_eq :
    cells.map (fun cell => cell.item.interval) = partition.intervals
  /-- Each original cell's weight is its exact signed endpoint difference. -/ weight_eq :
    ∀ cell ∈ cells, cell.weight = cell.item.interval.signedLength
  /-- Each original range encloses the actual source at every rational point in its closed domain. -/ source_range :
    ∀ cell ∈ cells, ∀ point, cell.item.interval.start ≤ point → point ≤ cell.item.interval.finish →
      cell.lower ≤ source point ∧ source point ≤ cell.upper

constructive_injectivity SourceFrontier

/-- Exact cell weights read back to the signed lengths of their original domain occurrences. -/
theorem integrationWeight_eq_lengthSum {α : Type} (domain : α → Partition.Interval) :
    ∀ (cells : List (IntegrationCell α)),
      (∀ cell ∈ cells, cell.weight = (domain cell.item).signedLength) →
      integrationWeight cells = Interval.lengthSum (cells.map (fun cell => domain cell.item))
  | [], _ => rfl
  | cell :: remaining, lengths => by
      have first := lengths cell List.mem_cons_self
      have rest := integrationWeight_eq_lengthSum domain remaining (fun other member =>
        lengths other (List.mem_cons_of_mem cell member))
      change cell.weight + integrationWeight remaining =
        (domain cell.item).signedLength + Interval.lengthSum (remaining.map (fun cell => domain cell.item))
      rw [first, rest]

namespace SourceFrontier

/-- Two source frontiers with the same partition and ordered cells are equal. -/
theorem ext {source : Fraction.Rational → Fraction.Rational} (left right : SourceFrontier source)
    (partition_eq : left.partition = right.partition) (cells_eq : left.cells = right.cells) : left = right := by
  cases left with
  | mk leftPartition leftCells leftDomains leftWeights leftRange =>
    cases right with
    | mk rightPartition rightCells rightDomains rightWeights rightRange =>
      cases partition_eq
      cases cells_eq
      rfl

/-- Read one original partition interval at its start and build its source-derived range cell.

The range constructor receives the same retained tag and cached source reading
stored in the result. The original interval occurrence supplies the exact weight. -/
@[expose] def rangeCell (source : Fraction.Rational → Fraction.Rational) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (entry : {interval // interval ∈ partition.intervals}) : IntegrationCell (SourcePoint source) :=
  let tag := SourcePoint.atStart source entry.val (partition.valid entry.val entry.property)
  let bound := range tag
  { item := tag
    weight := entry.val.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos (partition.valid entry.val entry.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- Build a cell using an observation retained at the interval start when one is available. -/
@[expose] def rangeCellCached (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (entry : {interval // interval ∈ partition.intervals}) : IntegrationCell (SourcePoint source) :=
  let tag := SourcePoint.atStartCached source cached entry.val (partition.valid entry.val entry.property)
  let bound := range tag
  { item := tag
    weight := entry.val.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos (partition.valid entry.val entry.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- A cache-selected cell is equal to the original fresh cell for the same interval occurrence. -/
theorem rangeCellCached_eq (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (entry : {interval // interval ∈ partition.intervals}) :
    rangeCellCached source cached partition range entry = rangeCell source partition range entry := by
  unfold rangeCellCached rangeCell
  rw [SourcePoint.atStartCached_eq]

/-- Build the original source frontier while reusing matching retained interval-start observations. -/
@[expose] def ofRangesCached (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (range_valid : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
        (range (SourcePoint.atStart source interval (partition.valid interval member))).Contains (source point)) :
    SourceFrontier source := by
  let makeCell := rangeCellCached source cached partition range
  let cells := partition.intervals.attach.map makeCell
  exact
    { partition := partition
      cells := cells
      domains_eq := by
        change (partition.intervals.attach.map makeCell).map (fun cell => cell.item.interval) = partition.intervals
        rw [Purelib.Data.List.Map.map_map]
        change partition.intervals.attach.map Subtype.val = partition.intervals
        exact Purelib.Data.List.attach_map_subtype_val _
      weight_eq := by
        intro cell member
        change cell ∈ partition.intervals.attach.map makeCell at member
        rcases (Purelib.Data.List.Map.mem_map).mp member with ⟨entry, _, equal⟩
        cases equal
        rfl
      source_range := by
        intro cell member point lower upper
        change cell ∈ partition.intervals.attach.map makeCell at member
        rcases (Purelib.Data.List.Map.mem_map).mp member with ⟨entry, _, equal⟩
        cases equal
        change entry.val.start ≤ point at lower
        change point ≤ entry.val.finish at upper
        change (range (SourcePoint.atStartCached source cached entry.val
          (partition.valid entry.val entry.property))).Contains (source point)
        rw [SourcePoint.atStartCached_eq]
        exact range_valid entry.val entry.property point lower upper }

/-- Build a source frontier by reading each original interval start and deriving its range from that reading.

The range constructor receives the cached point and reading. Its supplied law
must enclose the source throughout each original closed interval, rather than
only at the sampled endpoint. -/
@[expose] def ofRanges (source : Fraction.Rational → Fraction.Rational) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (range_valid : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
        (range (SourcePoint.atStart source interval (partition.valid interval member))).Contains (source point)) :
    SourceFrontier source :=
  ofRangesCached source [] partition range range_valid

/-- Cache-selected cells preserve the complete ordered original cell list. -/
theorem ofRangesCached_cells_eq (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (range_valid : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
        (range (SourcePoint.atStart source interval (partition.valid interval member))).Contains (source point)) :
    (ofRangesCached source cached partition range range_valid).cells =
      (ofRanges source partition range range_valid).cells := by
  change partition.intervals.attach.map (rangeCellCached source cached partition range) =
    partition.intervals.attach.map (rangeCell source partition range)
  apply Purelib.Data.List.Map.map_congr_left
  intro entry _
  exact rangeCellCached_eq source cached partition range entry

/-- Reusing saved readings preserves the complete original frontier. -/
theorem ofRangesCached_eq (source : Fraction.Rational → Fraction.Rational)
    (cached : List (SourcePoint source)) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (range_valid : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
        (range (SourcePoint.atStart source interval (partition.valid interval member))).Contains (source point)) :
    ofRangesCached source cached partition range range_valid = ofRanges source partition range range_valid :=
  ext _ _ rfl (ofRangesCached_cells_eq source cached partition range range_valid)

/-- Each constructed cell's oscillation is the width of its own retained reading-derived range. -/
theorem ofRanges_oscillation (source : Fraction.Rational → Fraction.Rational) (partition : Unit.Normalized)
    (range : SourcePoint source → Purelib.Data.Rat.Interval)
    (range_valid : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
        (range (SourcePoint.atStart source interval (partition.valid interval member))).Contains (source point))
    (cell : IntegrationCell (SourcePoint source))
    (member : cell ∈ (ofRanges source partition range range_valid).cells) :
    cell.oscillation = (range cell.item).width := by
  change cell ∈ partition.intervals.attach.map (rangeCell source partition range) at member
  rcases (Purelib.Data.List.Map.mem_map).mp member with ⟨entry, _, equal⟩
  cases equal
  rfl

/-- Every original frontier occurrence has its own exact length and pointwise source admission. -/
theorem admitted {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) (cell : IntegrationCell (SourcePoint source)) (member : cell ∈ frontier.cells) :
    IntegrationCell.Source.Admitted cell :=
  ⟨frontier.weight_eq cell member, frontier.source_range cell member⟩

/-- The exact weighted sum of the cached source readings at the retained tags. -/
@[expose] def taggedSum {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) : Fraction.Rational :=
  weightedEvaluation SourcePoint.reading frontier.cells

/-- Every retained tagged sum lies in the source frontier's original integral enclosure.

The pointwise source-range law is specialized at each actual tag; the cached
reading equality then supplies the existing finite weighted-evaluation bound. -/
theorem taggedSum_contains {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) :
    (integralBound frontier.cells).Contains frontier.taggedSum := by
  apply weightedEvaluation_mem_integralBound
  intro cell member
  have inside := frontier.source_range cell member cell.item.point cell.item.start_le cell.item.point_le_finish
  rw [cell.item.reading_eq]
  exact inside

/-- The enclosure width is exactly the retained length-weighted source oscillation. -/
theorem width_eq_oscillation {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) :
    (integralBound frontier.cells).width = integralOscillation frontier.cells :=
  integralBound_width frontier.cells

/-- The source frontier retains exact unit total weight, regardless of its tags and ranges. -/
theorem totalWeight {source : Fraction.Rational → Fraction.Rational}
    (frontier : SourceFrontier source) : integrationWeight frontier.cells = 1 := by
  rw [integrationWeight_eq_lengthSum (fun point : SourcePoint source => point.interval)
    frontier.cells frontier.weight_eq, frontier.domains_eq]
  exact frontier.partition.lengthSum

end SourceFrontier

end Purelib.Integration

end
