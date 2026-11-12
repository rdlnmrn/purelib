module
public import Purelib.Integration.Cell.Numerical.Continuous
public import Purelib.Computation.Query.Program
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing the original continuous numerical point requests

The exact prepared partition supplies the ordered query list. Each reply is
the original numerical point state and cached interval. Rebuilding cells
uses those replies directly; it does not rerun the point processes.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Continuous.Observation

open Purelib.Approximation
open Purelib.Computation.Query
open Purelib.Data.Rat

/-- One original interval occurrence in the prepared partition. -/
abbrev Entry {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) := {interval // interval ∈ prepared.partition.intervals}

/-- The original finite point-request construction over the prepared partition. -/
@[expose] def computation {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) :
    Program (Entry prepared) (NumericalPoint source) (List (Entry prepared × NumericalPoint source)) :=
  Program.record prepared.partition.intervals.attach

/-- Run the original point process at an actual retained partition occurrence. -/
@[expose] def originalReply {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (entry : Entry prepared) : NumericalPoint source :=
  NumericalPoint.atStart source entry.val (prepared.partition.valid entry.val entry.property) prepared.pointRequest

/-- Rebuild one cell from its original interval occurrence and already-returned numerical point. -/
@[expose] def cachedCell {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (entry : Entry prepared × NumericalPoint source) :
    IntegrationCell (NumericalPoint source) :=
  let bound := readingRange prepared.variation prepared.variationPositive.le entry.2
  { item := entry.2
    weight := entry.1.val.signedLength
    weight_nonnegative :=
      (Partition.Interval.signedLength_pos (prepared.partition.valid entry.1.val entry.1.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- A point certified as the actual observation selected for one original interval occurrence. -/
abbrev CachedPoint {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (entry : Entry prepared) :=
  {point : NumericalPoint source // point = (prepared.cachedStart cached entry).val}

set_option genInjectivity false in
/-- A numerical point reply retaining its original interval occurrence and actual selected process state. -/
structure CachedReply {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) where
  /-- The original interval occurrence for which this point was requested. -/ entry : Entry prepared
  /-- The actual selected point and its exact relation to the retained bank. -/ point :
    CachedPoint prepared cached entry

constructive_injectivity CachedReply

set_option genInjectivity false in
/-- A numerical reply for an occurrence other than the one actually requested. -/
structure InvalidEntry {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) where
  /-- The original requested interval occurrence. -/ requested : Entry prepared
  /-- The original interval occurrence reported by the reply. -/ reported : Entry prepared
  /-- The reported occurrence differs from the requested one. -/ different : reported ≠ requested

constructive_injectivity InvalidEntry

/-- Run the original point process for a displayed interval occurrence and retain its exact predecessor. -/
@[expose] def originalCachedReply {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    (entry : Entry prepared) : CachedReply prepared cached :=
  ⟨entry, ⟨(prepared.cachedStart cached entry).val, rfl⟩⟩

/-- Reuse a sufficient point or display the actual numerical request for one original occurrence. -/
@[expose] def cachedPoint {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (entry : Entry prepared) :
    Program (Entry prepared) (CachedReply prepared cached)
      (Except (InvalidEntry prepared) (CachedPoint prepared cached entry)) :=
  match NumericalPoint.findSufficient cached entry.val.start prepared.pointRequest with
  | some _ => .pure (.ok ⟨(prepared.cachedStart cached entry).val, rfl⟩)
  | none => .request entry fun reply =>
      if same : reply.entry = entry then .pure (.ok (same ▸ reply.point))
      else .pure (.error ⟨entry, reply.entry, same⟩)

/-- Original-source execution returns the exact point state used by the prepared numerical frontier. -/
theorem cachedPoint_original {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (entry : Entry prepared) :
    ((cachedPoint prepared cached entry).protocol.run (originalCachedReply prepared cached)).value =
      .ok ⟨(prepared.cachedStart cached entry).val, rfl⟩ := by
  unfold cachedPoint
  cases found : NumericalPoint.findSufficient cached entry.val.start prepared.pointRequest with
  | some retained => rfl
  | none =>
      change (((if same : (originalCachedReply prepared cached entry).entry = entry then
        (Program.pure (.ok (same ▸ (originalCachedReply prepared cached entry).point)) :
          Program (Entry prepared) (CachedReply prepared cached)
            (Except (InvalidEntry prepared) (CachedPoint prepared cached entry)))
        else Program.pure (.error ⟨entry, (originalCachedReply prepared cached entry).entry, same⟩)).protocol).run
          (originalCachedReply prepared cached)).value = _
      have same : (originalCachedReply prepared cached entry).entry = entry := rfl
      rewrite [dif_pos same]
      rfl

/-- A sufficient point observation produces no displayed numerical request. -/
theorem cachedPoint_hit_trace {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    (entry : Entry prepared) (retained : {point : NumericalPoint source // point.point = entry.val.start ∧
      point.reading.width < prepared.pointRequest.tolerance})
    (found : NumericalPoint.findSufficient cached entry.val.start prepared.pointRequest = some retained)
    (oracle : Entry prepared → CachedReply prepared cached) :
    ((cachedPoint prepared cached entry).protocol.run oracle).trace = [] := by
  unfold cachedPoint
  rewrite [found]
  rfl

/-- A requested numerical point carries its actual returned state and saved predecessor in the reply. -/
theorem cachedPoint_reply {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (entry : Entry prepared)
    (reply : CachedReply prepared cached) (same : reply.entry = entry) :
    (same ▸ reply.point).val = (prepared.cachedStart cached entry).val :=
  (same ▸ reply.point).property

/-- A numerical miss with the wrong returned occurrence reports that exact finite obstruction. -/
theorem cachedPoint_invalid {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) (entry : Entry prepared)
    (missing : NumericalPoint.findSufficient cached entry.val.start prepared.pointRequest = none)
    (oracle : Entry prepared → CachedReply prepared cached) (different : (oracle entry).entry ≠ entry) :
    ((cachedPoint prepared cached entry).protocol.run oracle).value =
      .error ⟨entry, (oracle entry).entry, different⟩ := by
  unfold cachedPoint
  rw [missing]
  change (((if same : (oracle entry).entry = entry then
    (Program.pure (.ok (same ▸ (oracle entry).point)) :
      Program (Entry prepared) (CachedReply prepared cached)
        (Except (InvalidEntry prepared) (CachedPoint prepared cached entry)))
    else Program.pure (.error ⟨entry, (oracle entry).entry, same⟩)).protocol).run oracle).value = _
  rw [dif_neg different]
  rfl

/-- A numerical cache miss makes exactly one displayed point request, even for an invalid reply. -/
theorem cachedPoint_miss_trace {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) (entry : Entry prepared)
    (missing : NumericalPoint.findSufficient cached entry.val.start prepared.pointRequest = none)
    (oracle : Entry prepared → CachedReply prepared cached) :
    ((cachedPoint prepared cached entry).protocol.run oracle).trace = [⟨entry, oracle entry⟩] := by
  unfold cachedPoint
  rw [missing]
  by_cases same : (oracle entry).entry = entry
  · change ⟨entry, oracle entry⟩ :: ((if same : (oracle entry).entry = entry then
      (Program.pure (.ok (same ▸ (oracle entry).point)) :
        Program (Entry prepared) (CachedReply prepared cached)
          (Except (InvalidEntry prepared) (CachedPoint prepared cached entry)))
      else Program.pure (.error ⟨entry, (oracle entry).entry, same⟩)).protocol.run oracle).trace = _
    rewrite [dif_pos same]
    rfl
  · change ⟨entry, oracle entry⟩ :: ((if same : (oracle entry).entry = entry then
      (Program.pure (.ok (same ▸ (oracle entry).point)) :
        Program (Entry prepared) (CachedReply prepared cached)
          (Except (InvalidEntry prepared) (CachedPoint prepared cached entry)))
      else Program.pure (.error ⟨entry, (oracle entry).entry, same⟩)).protocol.run oracle).trace = _
    rewrite [dif_neg same]
    rfl

/-- The exact ordered numerical cells selected for displayed original partition occurrences. -/
abbrev CachedCells {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (entries : List (Entry prepared)) :=
  {cells : List (IntegrationCell (NumericalPoint source)) // cells = entries.map
    (NumericalFrontier.selectedRangeCell source prepared.partition prepared.pointRequest
      (readingRange prepared.variation prepared.variationPositive.le) (prepared.cachedStart cached))}

/-- Add one returned numerical point to the already returned and certified remaining cells. -/
@[expose] def prependCell {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) (cached : List (NumericalPoint source)) (entry : Entry prepared)
    (remaining : List (Entry prepared)) (point : CachedPoint prepared cached entry)
    (tail : CachedCells prepared cached remaining) : CachedCells prepared cached (entry :: remaining) := by
  let cell := cachedCell prepared (entry, point.val)
  have same : cell = NumericalFrontier.selectedRangeCell source prepared.partition prepared.pointRequest
      (readingRange prepared.variation prepared.variationPositive.le) (prepared.cachedStart cached) entry := by
    change cachedCell prepared (entry, point.val) = _
    rw [point.property]
    rfl
  exact ⟨cell :: tail.val, congrArg₂ List.cons same tail.property⟩

/-- Construct numerical cells from the actual selected states and ordered source replies. -/
@[expose] def certifiedCells {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) :
    (entries : List (Entry prepared)) → Program (Entry prepared) (CachedReply prepared cached)
      (Except (InvalidEntry prepared) (CachedCells prepared cached entries))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | entry :: remaining =>
      (cachedPoint prepared cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (certifiedCells prepared cached remaining).map
            (fun after => after.map (prependCell prepared cached entry remaining point))

/-- Original numerical execution returns the selected point cells with their construction certificate. -/
theorem certifiedCells_original {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) :
    ∀ entries : List (Entry prepared),
      ((certifiedCells prepared cached entries).protocol.run (originalCachedReply prepared cached)).value =
        .ok ⟨entries.map (NumericalFrontier.selectedRangeCell source prepared.partition prepared.pointRequest
          (readingRange prepared.variation prepared.variationPositive.le) (prepared.cachedStart cached)), rfl⟩
  | [] => rfl
  | entry :: remaining => by
      change (((cachedPoint prepared cached entry).bind fun result =>
        match result with
        | .error invalid => .pure (.error invalid)
        | .ok point => (certifiedCells prepared cached remaining).map
            (fun after => after.map (prependCell prepared cached entry remaining point))).protocol.run
          (originalCachedReply prepared cached)).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, cachedPoint_original]
      rw [Program.map_execution, Protocol.map_run_value, certifiedCells_original prepared cached remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      rfl

/-- A wrong first numerical reply stops before any later point request. -/
theorem certifiedCells_invalid_first {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) (entry : Entry prepared) (remaining : List (Entry prepared))
    (missing : NumericalPoint.findSufficient cached entry.val.start prepared.pointRequest = none)
    (oracle : Entry prepared → CachedReply prepared cached) (different : (oracle entry).entry ≠ entry) :
    ((certifiedCells prepared cached (entry :: remaining)).protocol.run oracle).value =
        .error ⟨entry, (oracle entry).entry, different⟩ ∧
      ((certifiedCells prepared cached (entry :: remaining)).protocol.run oracle).trace = [⟨entry, oracle entry⟩] := by
  constructor
  · change (((cachedPoint prepared cached entry).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok point => (certifiedCells prepared cached remaining).map
          (fun after => after.map (prependCell prepared cached entry remaining point))).protocol.run oracle).value = _
    rw [Program.bind_execution, Protocol.bind_run_value,
      cachedPoint_invalid prepared cached entry missing oracle different]
    rfl
  · change (((cachedPoint prepared cached entry).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok point => (certifiedCells prepared cached remaining).map
          (fun after => after.map (prependCell prepared cached entry remaining point))).protocol.run oracle).trace = _
    rw [Program.bind_execution, Protocol.bind_run_trace,
      cachedPoint_invalid prepared cached entry missing oracle different,
      cachedPoint_miss_trace prepared cached entry missing oracle]
    rfl

/-- Assemble the complete cache-aware numerical result from the returned cells without another point request. -/
@[expose] def resultFromCells {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    (returned : CachedCells prepared cached prepared.partition.intervals.attach) : CachedResult modulus := by
  have cells_eq : returned.val = (prepared.frontierCached cached).cells := returned.property
  let frontier : NumericalFrontier source :=
    { partition := prepared.partition
      cells := returned.val
      domains_eq := (congrArg (List.map (fun cell : IntegrationCell (NumericalPoint source) => cell.item.interval))
        cells_eq).trans (prepared.frontierCached cached).domains_eq
      weight_eq := by
        intro cell member
        have original : cell ∈ (prepared.frontierCached cached).cells := cells_eq ▸ member
        exact (prepared.frontierCached cached).weight_eq cell original
      source_overlap := by
        intro cell member point lower upper state
        have original : cell ∈ (prepared.frontierCached cached).cells := cells_eq ▸ member
        exact (prepared.frontierCached cached).source_overlap cell original point lower upper state }
  have same : frontier = prepared.frontierCached cached := NumericalFrontier.ext frontier _ rfl cells_eq
  exact ⟨prepared, cached, frontier, same, same.symm ▸ prepared.frontierCached_width_lt cached⟩

/-- Returned cells assemble into the exact original cached numerical result. -/
theorem resultFromCells_eq {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (cached : List (NumericalPoint source))
    (request : AccuracyRequest)
    (returned : CachedCells (Preparation.prepare modulus request) cached
      (Preparation.prepare modulus request).partition.intervals.attach) :
    resultFromCells (Preparation.prepare modulus request) cached returned =
      CachedResult.build modulus cached request := by
  refine CachedResult.ext _ _ rfl rfl ?_
  refine NumericalFrontier.ext _ _ rfl ?_
  exact returned.property

/-- A complete returned result certified as the original cached producer request. -/
abbrev CertifiedResult {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :=
  {result : CachedResult modulus // result = CachedResult.build modulus cached request}

/-- Construct the original certified numerical result from one retained preparation and its returned cells. -/
@[expose] def certifiedResultPrepared {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (cached : List (NumericalPoint source)) (request : AccuracyRequest)
    (prepared : Preparation modulus) (same : prepared = Preparation.prepare modulus request) :
    Program (Entry prepared) (CachedReply prepared cached) (Except (InvalidEntry prepared)
      (CertifiedResult modulus cached request)) :=
  (certifiedCells prepared cached prepared.partition.intervals.attach).map fun returned =>
    returned.map fun cells => ⟨resultFromCells prepared cached cells, by
      cases same
      exact resultFromCells_eq modulus cached request cells⟩

/-- Build the complete original numerical result from returned certified point cells. -/
@[expose] def certifiedResultComputation {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    Program (Entry prepared) (CachedReply prepared cached) (Except (InvalidEntry prepared)
      (CertifiedResult modulus cached request)) :=
  certifiedResultPrepared modulus cached request (Preparation.prepare modulus request) rfl

/-- The certified numerical program returns the actual original cache-aware producer result. -/
theorem certifiedResult_original {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((certifiedResultComputation modulus cached request).protocol.run (originalCachedReply prepared cached)).value =
      .ok ⟨CachedResult.build modulus cached request, rfl⟩ := by
  let prepared := Preparation.prepare modulus request
  change ((certifiedResultComputation modulus cached request).protocol.run
    (originalCachedReply prepared cached)).value = _
  unfold certifiedResultComputation certifiedResultPrepared
  rw [Program.map_execution, Protocol.map_run_value, certifiedCells_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact resultFromCells_eq modulus cached request _

/-- Construct the original complete numerical result from its actual returned point observations. -/
@[expose] def cachedResultComputation {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) :
    Program (Entry prepared) (CachedReply prepared cached) (Except (InvalidEntry prepared) (CachedResult modulus)) :=
  (certifiedCells prepared cached prepared.partition.intervals.attach).map
    (fun returned => returned.map (resultFromCells prepared cached))

/-- Original numerical execution returns the complete actual cache-aware producer result. -/
theorem cachedResult_original {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    ((cachedResultComputation prepared cached).protocol.run (originalCachedReply prepared cached)).value =
      .ok (CachedResult.build modulus cached request) := by
  let prepared := Preparation.prepare modulus request
  change ((cachedResultComputation prepared cached).protocol.run (originalCachedReply prepared cached)).value = _
  unfold cachedResultComputation
  rw [Program.map_execution, Protocol.map_run_value, certifiedCells_original]
  apply congrArg Except.ok
  refine CachedResult.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · refine NumericalFrontier.ext _ _ ?_ ?_
    · rfl
    · rfl

/-- Exact replay returns the complete original cache-aware numerical result without point requests. -/
theorem cachedResult_replay {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) :
    let prepared := Preparation.prepare modulus request
    let program := cachedResultComputation prepared cached
    program.protocol.replayExact (program.protocol.run (originalCachedReply prepared cached)).trace =
      .ok (.ok (CachedResult.build modulus cached request)) := by
  let prepared := Preparation.prepare modulus request
  let program := cachedResultComputation prepared cached
  change program.protocol.replayExact (program.protocol.run (originalCachedReply prepared cached)).trace = _
  rw [program.protocol.replayExact_run, cachedResult_original]

/-- Replies outside the displayed numerical requests preserve the complete returned result and ordered trace. -/
theorem cachedResult_payload_erasure {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source))
    {Payload : Type} (payload : Payload) (outside : Payload → Entry prepared → CachedReply prepared cached) :
    let program := cachedResultComputation prepared cached
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (originalCachedReply prepared cached)).trace
      (outside payload)) = program.protocol.run (originalCachedReply prepared cached) :=
  (cachedResultComputation prepared cached).protocol.annotation_erasure (originalCachedReply prepared cached)
    payload outside

/-- The complete original trace is exactly the ordered prepared intervals paired with their original point replies. -/
theorem original_trace {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) :
    ((computation prepared).protocol.run (originalReply prepared)).trace =
      prepared.partition.intervals.attach.map (fun entry => ⟨entry, originalReply prepared entry⟩) :=
  Program.record_trace (originalReply prepared) prepared.partition.intervals.attach

/-- Original-source execution rebuilds exactly the cells used by the original numerical frontier.

The source oracle runs the same point request once per retained interval.
Each returned point is reused directly in the cell list, preserving its
original state, reading, range and order. -/
theorem original_cells {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) :
    (((computation prepared).protocol.run (originalReply prepared)).value.map (cachedCell prepared)) =
      prepared.frontier.cells := by
  unfold computation
  rw [Program.record_value]
  rw [Purelib.Data.List.Map.map_map]
  rfl

/-- Exact replay of the recorded original point requests returns the same retained replies. -/
theorem recorded_replay {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) :
    (computation prepared).protocol.replayExact
        ((computation prepared).protocol.run (originalReply prepared)).trace =
      .ok ((computation prepared).protocol.run (originalReply prepared)).value :=
  (computation prepared).protocol.replayExact_run (originalReply prepared)

/-- Rebuilding from the exact replay recovers the original complete cell list without source calls. -/
theorem replay_cells {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) :
    ((computation prepared).protocol.replayExact
      ((computation prepared).protocol.run (originalReply prepared)).trace).map (List.map (cachedCell prepared)) =
        .ok prepared.frontier.cells := by
  rw [recorded_replay]
  change Except.ok (((computation prepared).protocol.run (originalReply prepared)).value.map
    (cachedCell prepared)) = Except.ok prepared.frontier.cells
  rw [original_cells]

/-- Replies outside the recorded point-request trace do not change the complete original execution. -/
theorem payload_erasure {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (prepared : Preparation modulus) {Payload : Type} (payload : Payload)
    (outside : Payload → Entry prepared → NumericalPoint source) :
    (computation prepared).protocol.run (Boundary.Trace.overlay
      ((computation prepared).protocol.run (originalReply prepared)).trace (outside payload)) =
        (computation prepared).protocol.run (originalReply prepared) :=
  (computation prepared).protocol.annotation_erasure (originalReply prepared) payload outside

end Purelib.Integration.NumericalFrontier.Continuous.Observation

end
