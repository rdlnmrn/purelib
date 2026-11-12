module
public import Purelib.Integration.Cell.Source.Continuous
public import Purelib.Computation.Query.Program
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing original continuous exact-source readings

The prepared partition supplies the ordered query list. Each original reply
is its exact rational tag and cached source reading. Rebuilding cells uses
those returned readings directly.
-/

public section

namespace Purelib.Integration.SourceFrontier.Continuous.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat

/-- One original interval occurrence in the prepared partition. -/
abbrev Entry {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) := {interval // interval ∈ prepared.partition.intervals}

/-- The original finite exact-source reading construction over the prepared partition. -/
@[expose] def computation {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) :
    Program (Entry prepared) (SourcePoint source) (List (Entry prepared × SourcePoint source)) :=
  Program.record prepared.partition.intervals.attach

/-- Read the original source at an actual retained partition occurrence. -/
@[expose] def originalReply {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (entry : Entry prepared) : SourcePoint source :=
  SourcePoint.atStart source entry.val (prepared.partition.valid entry.val entry.property)

/-- Rebuild one cell from its original interval occurrence and already-returned source tag. -/
@[expose] def cachedCell {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (entry : Entry prepared × SourcePoint source) :
    IntegrationCell (SourcePoint source) :=
  let bound := readingRange prepared.variation prepared.variationPositive.le entry.2
  { item := entry.2
    weight := entry.1.val.signedLength
    weight_nonnegative :=
      (Partition.Interval.signedLength_pos (prepared.partition.valid entry.1.val entry.1.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

set_option genInjectivity false in
/-- A source reply whose original rational tag differs from the requested partition start. -/
structure InvalidTag {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) where
  /-- The original partition occurrence whose reading was requested. -/ entry : Entry prepared
  /-- The rational tag actually returned by the source reply. -/ reported : Fraction.Rational
  /-- The reported tag is not the requested original interval start. -/ different : reported ≠ entry.val.start

constructive_injectivity InvalidTag

/-- Place an already returned exact source reading at its matching original interval start. -/
@[expose] def acquired {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (entry : Entry prepared) (reply : SourcePoint source)
    (same : reply.point = entry.val.start) : SourcePoint source :=
  ⟨entry.val, entry.val.start, le_rfl, (prepared.partition.valid entry.val entry.property).2.1.le,
    reply.reading, reply.reading_eq.trans (congrArg source same)⟩

/-- An acquired matching source reading is the same exact point as the original fresh request. -/
theorem acquired_eq_start {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (entry : Entry prepared) (reply : SourcePoint source)
    (same : reply.point = entry.val.start) :
    acquired prepared entry reply same = SourcePoint.atStart source entry.val
      (prepared.partition.valid entry.val entry.property) := by
  unfold acquired SourcePoint.atStart SourcePoint.observe
  simp only [-eq_self, -iff_self, reply.reading_eq, same]
  rfl

/-- Every matching acquired point equals the original preparation's cache-selected start point. -/
theorem acquired_eq_cached {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (cached : List (SourcePoint source)) (entry : Entry prepared)
    (reply : SourcePoint source) (same : reply.point = entry.val.start) :
    acquired prepared entry reply same = SourcePoint.atStartCached source cached entry.val
      (prepared.partition.valid entry.val entry.property) :=
  (acquired_eq_start prepared entry reply same).trans
    (SourcePoint.atStartCached_eq source cached entry.val (prepared.partition.valid entry.val entry.property)).symm

/-- A returned point certified as the actual cache-selected observation of one original occurrence. -/
abbrev CachedPoint {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (cached : List (SourcePoint source)) (entry : Entry prepared) :=
  {point : SourcePoint source // point = SourcePoint.atStartCached source cached entry.val
    (prepared.partition.valid entry.val entry.property)}

/-- Read one prepared interval start from the saved bank or one displayed source request. -/
@[expose] def cachedPoint {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (entry : Entry prepared) : Program (Entry prepared) (SourcePoint source) (Except (InvalidTag prepared)
      (CachedPoint prepared cached entry)) :=
  match SourcePoint.findCached cached entry.val.start with
  | some retained => .pure (.ok ⟨acquired prepared entry retained.val retained.property,
      acquired_eq_cached prepared cached entry retained.val retained.property⟩)
  | none => .request entry fun reply =>
      if same : reply.point = entry.val.start then .pure (.ok ⟨acquired prepared entry reply same,
        acquired_eq_cached prepared cached entry reply same⟩)
      else .pure (.error ⟨entry, reply.point, same⟩)

/-- Request only source readings absent from the original retained exact bank.

Each cache hit supplies the saved source point directly. A miss requests the
actual partition occurrence, checks its returned tag, and consumes the same
reply when constructing the cell list. An invalid tag stops before later
source requests. -/
@[expose] def cachedComputation {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    List (Entry prepared) → Program (Entry prepared) (SourcePoint source)
      (Except (InvalidTag prepared) (List (Entry prepared × SourcePoint source)))
  | [] => .pure (.ok [])
  | entry :: remaining =>
      (cachedPoint prepared cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (cachedComputation prepared cached remaining).map
            (fun after => after.map (fun rest => (entry, point.val) :: rest))

/-- Original-source execution of one cached lookup returns the actual point used by the prepared frontier. -/
theorem cachedPoint_original {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (cached : List (SourcePoint source)) (entry : Entry prepared) :
    ((cachedPoint prepared cached entry).protocol.run (originalReply prepared)).value =
      .ok ⟨SourcePoint.atStartCached source cached entry.val (prepared.partition.valid entry.val entry.property),
        rfl⟩ := by
  unfold cachedPoint
  cases found : SourcePoint.findCached cached entry.val.start with
  | none =>
      change (((if same : (originalReply prepared entry).point = entry.val.start then
        (Program.pure (.ok ⟨acquired prepared entry (originalReply prepared entry) same,
          acquired_eq_cached prepared cached entry (originalReply prepared entry) same⟩) :
          Program (Entry prepared) (SourcePoint source)
            (Except (InvalidTag prepared) (CachedPoint prepared cached entry)))
        else Program.pure (.error ⟨entry, (originalReply prepared entry).point, same⟩)).protocol).run
          (originalReply prepared)).value = _
      have same : (originalReply prepared entry).point = entry.val.start := rfl
      rw [dif_pos same]
      apply congrArg Except.ok
      apply Subtype.ext
      exact acquired_eq_cached prepared cached entry (originalReply prepared entry) same
  | some retained =>
      apply congrArg Except.ok
      apply Subtype.ext
      exact acquired_eq_cached prepared cached entry retained.val retained.property

/-- The exact ordered cells selected for a displayed list of original partition occurrences. -/
abbrev CachedCells {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (cached : List (SourcePoint source)) (entries : List (Entry prepared)) :=
  {cells : List (IntegrationCell (SourcePoint source)) // cells = entries.map
    (SourceFrontier.rangeCellCached source cached prepared.partition
      (readingRange prepared.variation prepared.variationPositive.le))}

/-- Add one returned point to the already returned and certified remaining cells. -/
@[expose] def prependCell {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) (cached : List (SourcePoint source)) (entry : Entry prepared)
    (remaining : List (Entry prepared)) (point : CachedPoint prepared cached entry)
    (tail : CachedCells prepared cached remaining) : CachedCells prepared cached (entry :: remaining) := by
  let cell := cachedCell prepared (entry, point.val)
  have same : cell = SourceFrontier.rangeCellCached source cached prepared.partition
      (readingRange prepared.variation prepared.variationPositive.le) entry := by
    change cachedCell prepared (entry, point.val) = _
    rw [point.property]
    rfl
  exact ⟨cell :: tail.val, congrArg₂ List.cons same tail.property⟩

/-- Construct certified cells from the same ordered cache hits and returned source replies. -/
@[expose] def certifiedCells {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    (entries : List (Entry prepared)) → Program (Entry prepared) (SourcePoint source)
      (Except (InvalidTag prepared) (CachedCells prepared cached entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining =>
      (cachedPoint prepared cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (certifiedCells prepared cached remaining).map
            (fun after => after.map (prependCell prepared cached entry remaining point))

/-- Original-source execution returns the exact selected cells with their retained construction certificate. -/
theorem certifiedCells_original {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    ∀ entries : List (Entry prepared),
      ((certifiedCells prepared cached entries).protocol.run (originalReply prepared)).value =
        .ok ⟨entries.map (SourceFrontier.rangeCellCached source cached prepared.partition
          (readingRange prepared.variation prepared.variationPositive.le)), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((cachedPoint prepared cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (certifiedCells prepared cached remaining).map
            (fun after => after.map (prependCell prepared cached entry remaining point))).protocol.run
          (originalReply prepared)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, cachedPoint_original]
      rw [Program.map_execution, Protocol.map_run_value, certifiedCells_original prepared cached remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      rfl

/-- Assemble the original complete continuous result from returned certified cells without rereading the source. -/
@[expose] def resultFromCells {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (returned : CachedCells prepared cached prepared.partition.intervals.attach) : Result modulus := by
  have cells_eq : returned.val = (prepared.frontierCached cached).cells := returned.property
  let frontier : SourceFrontier source :=
    { partition := prepared.partition
      cells := returned.val
      domains_eq := (congrArg (List.map (fun cell : IntegrationCell (SourcePoint source) => cell.item.interval))
        cells_eq).trans (prepared.frontierCached cached).domains_eq
      weight_eq := by
        intro cell member
        have original : cell ∈ (prepared.frontierCached cached).cells := cells_eq ▸ member
        exact (prepared.frontierCached cached).weight_eq cell original
      source_range := by
        intro cell member point lower upper
        have original : cell ∈ (prepared.frontierCached cached).cells := cells_eq ▸ member
        exact (prepared.frontierCached cached).source_range cell original point lower upper }
  have same : frontier = prepared.frontier :=
    (SourceFrontier.ext frontier (prepared.frontierCached cached) rfl cells_eq).trans
      (prepared.frontierCached_eq cached)
  exact ⟨prepared, frontier, same, same.symm ▸ prepared.frontier_width_lt⟩

/-- Any returned certified cells assemble to the actual original cache-aware producer result. -/
theorem resultFromCells_eq_build {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (returned : CachedCells (Preparation.prepare modulus request) cached
      (Preparation.prepare modulus request).partition.intervals.attach) :
    resultFromCells (Preparation.prepare modulus request) cached returned = buildCached modulus cached request := by
  refine Result.ext _ _ ?_ ?_
  · rfl
  · refine SourceFrontier.ext _ _ ?_ ?_
    · rfl
    · exact returned.property

/-- A complete continuous result certified as the actual cache-aware producer output. -/
abbrev CertifiedResult {source : Fraction.Rational → Fraction.Rational} (modulus : Rational.Uniform.Modulus source)
    (cached : List (SourcePoint source)) (request : AccuracyRequest) :=
  {result : Result modulus // result = buildCached modulus cached request}

/-- Construct the original certified result from one retained preparation and its returned source points. -/
@[expose] def certifiedResultPrepared {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest)
    (prepared : Preparation modulus) (same : prepared = Preparation.prepare modulus request) :
    Program (Entry prepared) (SourcePoint source)
      (Except (InvalidTag prepared) (CertifiedResult modulus cached request)) :=
  (certifiedCells prepared cached prepared.partition.intervals.attach).map fun returned =>
    returned.map fun cells =>
      ⟨resultFromCells prepared cached cells, by
        cases same
        exact resultFromCells_eq_build modulus cached request cells⟩

/-- Return the original producer result together with its exact cache-aware construction certificate. -/
@[expose] def certifiedResultComputation {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Entry prepared) (SourcePoint source)
      (Except (InvalidTag prepared) (CertifiedResult modulus cached request)) :=
  certifiedResultPrepared modulus cached request (Preparation.prepare modulus request) rfl

/-- The certified result construction returns the exact original cache-aware result under its original source. -/
theorem certifiedResult_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((certifiedResultComputation modulus cached request).protocol.run (originalReply prepared)).value =
      .ok ⟨buildCached modulus cached request, rfl⟩ := by
  let prepared := Preparation.prepare modulus request
  change ((certifiedResultComputation modulus cached request).protocol.run (originalReply prepared)).value = _
  unfold certifiedResultComputation certifiedResultPrepared
  rw [Program.map_execution, Protocol.map_run_value, certifiedCells_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact resultFromCells_eq_build modulus cached request _

/-- Construct the complete original result from cache hits and the actual returned exact source replies. -/
@[expose] def cachedResultComputation {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    Program (Entry prepared) (SourcePoint source) (Except (InvalidTag prepared) (Result modulus)) :=
  (certifiedCells prepared cached prepared.partition.intervals.attach).map
    (fun returned => returned.map (resultFromCells prepared cached))

/-- Original-source execution returns the complete actual cache-aware continuous producer result. -/
theorem cachedResult_original {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((cachedResultComputation prepared cached).protocol.run (originalReply prepared)).value =
      .ok (buildCached modulus cached request) := by
  let prepared := Preparation.prepare modulus request
  change ((cachedResultComputation prepared cached).protocol.run (originalReply prepared)).value = _
  unfold cachedResultComputation
  rw [Program.map_execution, Protocol.map_run_value, certifiedCells_original]
  apply congrArg Except.ok
  refine Result.ext _ _ ?_ ?_
  · rfl
  · refine SourceFrontier.ext _ _ ?_ ?_
    · rfl
    · rfl

/-- The complete result construction retains the same ordered source trace as its returned certified cells. -/
theorem cachedResult_trace {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (oracle : Entry prepared → SourcePoint source) :
    ((cachedResultComputation prepared cached).protocol.run oracle).trace =
      ((certifiedCells prepared cached prepared.partition.intervals.attach).protocol.run oracle).trace := by
  unfold cachedResultComputation
  rw [Program.map_execution, Protocol.map_run_trace]

/-- Exact replay returns the complete original cache-aware continuous result without source requests. -/
theorem cachedResult_replay {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Uniform.Modulus source) (cached : List (SourcePoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := cachedResultComputation prepared cached
    program.protocol.replayExact (program.protocol.run (originalReply prepared)).trace =
      .ok (.ok (buildCached modulus cached request)) := by
  let prepared := Preparation.prepare modulus request
  let program := cachedResultComputation prepared cached
  change program.protocol.replayExact (program.protocol.run (originalReply prepared)).trace = _
  rw [program.protocol.replayExact_run, cachedResult_original]

/-- Replies outside the executed cache-aware result trace preserve the complete result and ordered trace. -/
theorem cachedResult_payload_erasure {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    {Payload : Type} (payload : Payload) (outside : Payload → Entry prepared → SourcePoint source) :
    let program := cachedResultComputation prepared cached
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (originalReply prepared)).trace
      (outside payload)) = program.protocol.run (originalReply prepared) :=
  (cachedResultComputation prepared cached).protocol.annotation_erasure (originalReply prepared) payload outside

/-- Original-source execution returns the actual cache-selected points in the original occurrence order. -/
theorem cachedComputation_original {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    ∀ entries : List (Entry prepared),
      ((cachedComputation prepared cached entries).protocol.run (originalReply prepared)).value =
        .ok (entries.map (fun entry => (entry, SourcePoint.atStartCached source cached entry.val
          (prepared.partition.valid entry.val entry.property))))
  | [] => rfl
  | entry :: remaining => by
      change (((cachedPoint prepared cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (cachedComputation prepared cached remaining).map
            (fun after => after.map (fun rest => (entry, point.val) :: rest))).protocol.run
          (originalReply prepared)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, cachedPoint_original]
      rw [Program.map_execution, Protocol.map_run_value, cachedComputation_original prepared cached remaining]
      rfl

/-- Original cached execution rebuilds the exact cells consumed by the actual prepared frontier. -/
theorem cached_original_cells {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    (((cachedComputation prepared cached prepared.partition.intervals.attach).protocol.run
      (originalReply prepared)).value.map (List.map (cachedCell prepared))) =
        .ok (prepared.frontierCached cached).cells := by
  rw [cachedComputation_original]
  change Except.ok (((prepared.partition.intervals.attach.map fun entry =>
    (entry, SourcePoint.atStartCached source cached entry.val (prepared.partition.valid entry.val entry.property))).map
      (cachedCell prepared))) = _
  rw [Purelib.Data.List.Map.map_map]
  rfl

/-- Replaying the original cached trace rebuilds the same complete prepared cell list without source requests. -/
theorem cached_replay_cells {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source)) :
    let program := cachedComputation prepared cached prepared.partition.intervals.attach
    ((program.protocol.replayExact (program.protocol.run (originalReply prepared)).trace).map
      (fun result => result.map (List.map (cachedCell prepared)))) =
        .ok (.ok (prepared.frontierCached cached).cells) := by
  let program := cachedComputation prepared cached prepared.partition.intervals.attach
  change (program.protocol.replayExact (program.protocol.run (originalReply prepared)).trace).map
    (fun result => result.map (List.map (cachedCell prepared))) = _
  rw [program.protocol.replayExact_run]
  change Except.ok (((program.protocol.run (originalReply prepared)).value).map (List.map (cachedCell prepared))) = _
  rw [cached_original_cells]

/-- Changes outside the actual cached-source requests preserve the complete ordered execution. -/
theorem cached_payload_erasure {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    {Payload : Type} (payload : Payload) (outside : Payload → Entry prepared → SourcePoint source) :
    let program := cachedComputation prepared cached prepared.partition.intervals.attach
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (originalReply prepared)).trace
      (outside payload)) =
      program.protocol.run (originalReply prepared) :=
  (cachedComputation prepared cached prepared.partition.intervals.attach).protocol.annotation_erasure
    (originalReply prepared) payload outside

/-- A cache hit produces no displayed source request for the actual original partition occurrence. -/
theorem cachedPoint_hit_trace {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (entry : Entry prepared) (retained : {point : SourcePoint source // point.point = entry.val.start})
    (found : SourcePoint.findCached cached entry.val.start = some retained)
    (oracle : Entry prepared → SourcePoint source) :
    ((cachedPoint prepared cached entry).protocol.run oracle).trace = [] := by
  unfold cachedPoint
  rewrite [found]
  rfl

/-- A cache miss makes exactly one displayed source request, including when the returned tag is invalid. -/
theorem cachedPoint_miss_trace {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (entry : Entry prepared) (missing : SourcePoint.findCached cached entry.val.start = none)
    (oracle : Entry prepared → SourcePoint source) :
    ((cachedPoint prepared cached entry).protocol.run oracle).trace = [⟨entry, oracle entry⟩] := by
  unfold cachedPoint
  rw [missing]
  by_cases same : (oracle entry).point = entry.val.start
  · change ⟨entry, oracle entry⟩ :: ((if same : (oracle entry).point = entry.val.start then
        (Program.pure (.ok ⟨acquired prepared entry (oracle entry) same,
          acquired_eq_cached prepared cached entry (oracle entry) same⟩) :
          Program (Entry prepared) (SourcePoint source)
            (Except (InvalidTag prepared) (CachedPoint prepared cached entry)))
        else Program.pure (.error ⟨entry, (oracle entry).point, same⟩)).protocol.run oracle).trace = _
    rewrite [dif_pos same]
    rfl
  · change ⟨entry, oracle entry⟩ :: ((if same : (oracle entry).point = entry.val.start then
        (Program.pure (.ok ⟨acquired prepared entry (oracle entry) same,
          acquired_eq_cached prepared cached entry (oracle entry) same⟩) :
          Program (Entry prepared) (SourcePoint source)
            (Except (InvalidTag prepared) (CachedPoint prepared cached entry)))
        else Program.pure (.error ⟨entry, (oracle entry).point, same⟩)).protocol.run oracle).trace = _
    rewrite [dif_neg same]
    rfl

/-- A cache miss with the wrong returned tag reports that exact finite obstruction. -/
theorem cachedPoint_invalid {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (entry : Entry prepared) (missing : SourcePoint.findCached cached entry.val.start = none)
    (oracle : Entry prepared → SourcePoint source) (different : (oracle entry).point ≠ entry.val.start) :
    ((cachedPoint prepared cached entry).protocol.run oracle).value =
      .error ⟨entry, (oracle entry).point, different⟩ := by
  unfold cachedPoint
  rw [missing]
  change (((if same : (oracle entry).point = entry.val.start then
    (Program.pure (.ok ⟨acquired prepared entry (oracle entry) same,
      acquired_eq_cached prepared cached entry (oracle entry) same⟩) :
      Program (Entry prepared) (SourcePoint source) (Except (InvalidTag prepared) (CachedPoint prepared cached entry)))
    else Program.pure (.error ⟨entry, (oracle entry).point, same⟩)).protocol).run oracle).value = _
  rw [dif_neg different]
  rfl

/-- An invalid first reply stops the cached computation before requesting any later interval. -/
theorem cachedComputation_invalid_first {source : Fraction.Rational → Fraction.Rational}
    {modulus : Rational.Uniform.Modulus source} (prepared : Preparation modulus) (cached : List (SourcePoint source))
    (entry : Entry prepared) (remaining : List (Entry prepared))
    (missing : SourcePoint.findCached cached entry.val.start = none)
    (oracle : Entry prepared → SourcePoint source) (different : (oracle entry).point ≠ entry.val.start) :
    ((cachedComputation prepared cached (entry :: remaining)).protocol.run oracle).value =
        .error ⟨entry, (oracle entry).point, different⟩ ∧
      ((cachedComputation prepared cached (entry :: remaining)).protocol.run oracle).trace =
        [⟨entry, oracle entry⟩] := by
  constructor
  · change (((cachedPoint prepared cached entry).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok point => (cachedComputation prepared cached remaining).map
          (fun after => after.map (fun rest => (entry, point.val) :: rest))).protocol.run oracle).value = _
    rw [Program.bind_execution, Protocol.bind_run_value,
      cachedPoint_invalid prepared cached entry missing oracle different]
    rfl
  · change (((cachedPoint prepared cached entry).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok point => (cachedComputation prepared cached remaining).map
          (fun after => after.map (fun rest => (entry, point.val) :: rest))).protocol.run oracle).trace = _
    rw [Program.bind_execution, Protocol.bind_run_trace,
      cachedPoint_invalid prepared cached entry missing oracle different,
      cachedPoint_miss_trace prepared cached entry missing oracle]
    rfl

/-- The complete original trace is the ordered prepared intervals paired with their original source replies. -/
theorem original_trace {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) :
    ((computation prepared).protocol.run (originalReply prepared)).trace =
      prepared.partition.intervals.attach.map (fun entry => ⟨entry, originalReply prepared entry⟩) :=
  Program.record_trace (originalReply prepared) prepared.partition.intervals.attach

/-- Original-source execution rebuilds exactly the cells used by the original exact-source frontier. -/
theorem original_cells {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) :
    (((computation prepared).protocol.run (originalReply prepared)).value.map (cachedCell prepared)) =
      prepared.frontier.cells := by
  unfold computation
  rw [Program.record_value, Purelib.Data.List.Map.map_map]
  rfl

/-- Exact replay of recorded source reads returns the same complete retained replies. -/
theorem recorded_replay {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) :
    (computation prepared).protocol.replayExact
        ((computation prepared).protocol.run (originalReply prepared)).trace =
      .ok ((computation prepared).protocol.run (originalReply prepared)).value :=
  (computation prepared).protocol.replayExact_run (originalReply prepared)

/-- Rebuilding from exact replay recovers the original complete cell list without source calls. -/
theorem replay_cells {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) :
    ((computation prepared).protocol.replayExact
      ((computation prepared).protocol.run (originalReply prepared)).trace).map (List.map (cachedCell prepared)) =
        .ok prepared.frontier.cells := by
  rw [recorded_replay]
  change Except.ok (((computation prepared).protocol.run (originalReply prepared)).value.map
    (cachedCell prepared)) = Except.ok prepared.frontier.cells
  rw [original_cells]

/-- Replies outside the recorded exact-source trace do not change the complete original execution. -/
theorem payload_erasure {source : Fraction.Rational → Fraction.Rational} {modulus : Rational.Uniform.Modulus source}
    (prepared : Preparation modulus) {Payload : Type} (payload : Payload)
    (outside : Payload → Entry prepared → SourcePoint source) :
    (computation prepared).protocol.run (Boundary.Trace.overlay
      ((computation prepared).protocol.run (originalReply prepared)).trace (outside payload)) =
        (computation prepared).protocol.run (originalReply prepared) :=
  (computation prepared).protocol.annotation_erasure (originalReply prepared) payload outside

end Purelib.Integration.SourceFrontier.Continuous.Observation

end
