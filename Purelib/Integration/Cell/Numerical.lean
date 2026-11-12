module
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Partition.Length
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite numerical point readings in integration cells

Each rational tag retains its original point process, previous state, actual
positive request, resulting state and cached rational interval. A numerical
frontier admits every finite point state by interval overlap rather than
assuming an exact point value.
-/

public section

namespace Purelib.Integration

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- A rational tag with one actual request to its original point-enclosure process.

The previous and returned states remain indexed by the original rational tag.
The cached interval is exactly the original process's readback of the
returned state; no exact rational value is selected from it. -/
structure NumericalPoint (source : Fraction.Rational → BoundProcess) where
  /-- The retained rational cell interval. -/ interval : Partition.Interval
  /-- The exact rational query point. -/ point : Fraction.Rational
  /-- The point is at or above the interval's start. -/ start_le : interval.start ≤ point
  /-- The point is at or below the interval's finish. -/ point_le_finish : point ≤ interval.finish
  /-- The original point-process state supplied to this request. -/ previous : (source point).State
  /-- The original positive point-width request. -/ request : AccuracyRequest
  /-- The actual state returned by the same original point process. -/ state : (source point).State
  /-- The state is the original request applied to the retained previous state. -/ state_eq :
    state = (source point).request previous request.tolerance request.positive
  /-- The cached rational enclosure read from that actual state. -/ reading : Purelib.Data.Rat.Interval
  /-- The cached enclosure is the original process readback. -/ reading_eq : reading = (source point).bound state

constructive_injectivity NumericalPoint

/-- Compare numerical points by their original tag, interval, predecessor and request.

The returned state and cached reading are determined by those fields. Equality
is executable when each original point process has executable state equality. -/
instance {source : Fraction.Rational → BoundProcess} [∀ point, DecidableEq (source point).State] :
    DecidableEq (NumericalPoint source) := by
  intro first second
  cases first with
  | mk firstInterval firstPoint firstLower firstUpper firstPrevious firstRequest firstState firstStateEq firstReading
      firstReadingEq =>
    cases second with
    | mk secondInterval secondPoint secondLower secondUpper secondPrevious secondRequest secondState secondStateEq
        secondReading secondReadingEq =>
      by_cases samePoint : firstPoint = secondPoint
      · cases samePoint
        by_cases sameInterval : firstInterval = secondInterval
        · cases sameInterval
          by_cases samePrevious : firstPrevious = secondPrevious
          · cases samePrevious
            by_cases sameRequest : firstRequest = secondRequest
            · cases sameRequest
              cases firstStateEq
              cases secondStateEq
              cases firstReadingEq
              cases secondReadingEq
              exact isTrue rfl
            · exact isFalse (fun same => sameRequest (congrArg NumericalPoint.request same))
          · exact isFalse (fun same => samePrevious (by cases same; rfl))
        · exact isFalse (fun same => sameInterval (congrArg NumericalPoint.interval same))
      · exact isFalse (fun same => samePoint (congrArg NumericalPoint.point same))

namespace NumericalPoint

/-- Request a numerical point enclosure from an explicitly retained previous state. -/
@[expose] def observe (source : Fraction.Rational → BoundProcess)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (previous : (source point).State) (request : AccuracyRequest) : NumericalPoint source :=
  let state := (source point).request previous request.tolerance request.positive
  ⟨interval, point, start_le, point_le_finish, previous, request, state, rfl, (source point).bound state, rfl⟩

/-- Assemble a point from the returned state and cached reading of its original request.

The supplied equalities bind both returned values to the same source and
predecessor. Assembly consumes those values without repeating either call. -/
@[expose] def observeWith (source : Fraction.Rational → BoundProcess)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (previous : (source point).State) (request : AccuracyRequest) (state : (source point).State)
    (state_eq : state = (source point).request previous request.tolerance request.positive)
    (reading : Purelib.Data.Rat.Interval) (reading_eq : reading = (source point).bound state) : NumericalPoint source :=
  ⟨interval, point, start_le, point_le_finish, previous, request, state, state_eq, reading, reading_eq⟩

/-- Returned state and reading assemble to the exact original numerical point. -/
theorem observeWith_eq (source : Fraction.Rational → BoundProcess)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (previous : (source point).State) (request : AccuracyRequest) (state : (source point).State)
    (state_eq : state = (source point).request previous request.tolerance request.positive)
    (reading : Purelib.Data.Rat.Interval) (reading_eq : reading = (source point).bound state) :
    observeWith source interval point start_le point_le_finish previous request state state_eq reading reading_eq =
      observe source interval point start_le point_le_finish previous request := by
  cases state_eq
  cases reading_eq
  rfl

/-- Request a numerical enclosure at the start of an original unit interval. -/
@[expose] def atStart (source : Fraction.Rational → BoundProcess)
    (interval : Partition.Interval) (valid : interval.Valid) (request : AccuracyRequest) : NumericalPoint source :=
  observe source interval interval.start le_rfl valid.2.1.le (source interval.start).initial request

/-- Refine the saved numerical point state with another positive request at the same tag. -/
@[expose] def refine {source : Fraction.Rational → BoundProcess}
    (retained : NumericalPoint source) (request : AccuracyRequest) : NumericalPoint source :=
  observe source retained.interval retained.point retained.start_le retained.point_le_finish retained.state request

/-- Reuse the saved point state when a new rational query has the same tag. -/
@[expose] def previousAt {source : Fraction.Rational → BoundProcess}
    (retained : NumericalPoint source) (point : Fraction.Rational) : (source point).State :=
  if equal : point = retained.point then equal.symm ▸ retained.state else (source point).initial

/-- Querying the original tag reuses its exact saved point-process state. -/
theorem previousAt_point {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source) :
    retained.previousAt retained.point = retained.state := by
  unfold previousAt
  rw [dif_pos rfl]

/-- The actual cached point reading meets its own original width request. -/
theorem reading_width_lt {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source) :
    retained.reading.width < retained.request.tolerance := by
  rw [retained.reading_eq, retained.state_eq]
  exact (source retained.point).accurate retained.previous retained.request.tolerance retained.request.positive

/-- Move a saved numerical point to another interval containing its unchanged rational tag. -/
@[expose] def move {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (same : point = retained.point) : NumericalPoint source := by
  cases same
  exact { retained with interval := interval, start_le := start_le, point_le_finish := point_le_finish }

/-- Moving a point retains its exact original rational tag. -/
theorem move_point {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational) (start_le : interval.start ≤ point)
    (point_le_finish : point ≤ interval.finish) (same : point = retained.point) :
    (retained.move interval point start_le point_le_finish same).point = point := by
  cases same
  rfl

/-- Moving a point retains its exact original cached interval. -/
theorem move_reading {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational) (start_le : interval.start ≤ point)
    (point_le_finish : point ≤ interval.finish) (same : point = retained.point) :
    (retained.move interval point start_le point_le_finish same).reading = retained.reading := by
  cases same
  rfl

/-- An observation at a displayed interval and rational tag with its original requested width. -/
abbrev Observation (source : Fraction.Rational → BoundProcess) (interval : Partition.Interval)
    (point : Fraction.Rational) (request : AccuracyRequest) :=
  {retained : NumericalPoint source // retained.interval = interval ∧ retained.point = point ∧
    retained.reading.width < request.tolerance}

/-- An interval-start observation with its original requested width. -/
abbrev StartObservation (source : Fraction.Rational → BoundProcess) (interval : Partition.Interval)
    (request : AccuracyRequest) := Observation source interval interval.start request

set_option genInjectivity false in
/-- A point decision either reuses an adequate original observation or requests its exact predecessor state. -/
inductive Selection (source : Fraction.Rational → BoundProcess) (point : Fraction.Rational)
    (request : AccuracyRequest) where
  /-- The actual saved observation has the requested tag and sufficient width. -/
  | reuse (retained : NumericalPoint source) (same : point = retained.point)
      (accurate : retained.reading.width < request.tolerance)
  /-- The original source must be requested from this exact point-process state. -/
  | request (previous : (source point).State)

namespace Selection

/-- The result needed to execute a selected branch, including the actual state and cached readback. -/
@[expose] def Reply {source : Fraction.Rational → BoundProcess} {point : Fraction.Rational}
    {request : AccuracyRequest} : Selection source point request → Type
  | .reuse _ _ _ => Unit
  | .request previous =>
      Σ state : {state : (source point).State //
        state = (source point).request previous request.tolerance request.positive},
        {reading : Purelib.Data.Rat.Interval // reading = (source point).bound state.val}

/-- Assemble the exact selected observation from the branch's supplied state and readback.

The saved branch moves the original observation; the requested branch uses
the returned state and interval. Neither branch repeats a point request. -/
@[expose] def resolveWith {source : Fraction.Rational → BoundProcess} {point : Fraction.Rational}
    {request : AccuracyRequest} (selection : Selection source point request) (interval : Partition.Interval)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (reply : selection.Reply) : Observation source interval point request := by
  cases selection with
  | reuse retained same accurate =>
      let selected := retained.move interval point start_le point_le_finish same
      have intervalEq : selected.interval = interval := by
        cases same
        rfl
      have width : selected.reading.width < request.tolerance := by
        rw [retained.move_reading interval point start_le point_le_finish same]
        exact accurate
      exact ⟨selected, intervalEq, retained.move_point interval point start_le point_le_finish same, width⟩
  | request previous =>
      let selected := observeWith source interval point start_le point_le_finish previous request
        reply.1.val reply.1.property reply.2.val reply.2.property
      exact ⟨selected, rfl, rfl, selected.reading_width_lt⟩

/-- Execute the selected original point request, or reuse its adequate saved observation. -/
@[expose] def resolve {source : Fraction.Rational → BoundProcess} {point : Fraction.Rational}
    {request : AccuracyRequest} (selection : Selection source point request) (interval : Partition.Interval)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish) :
    Observation source interval point request :=
  match selection with
  | .reuse retained same accurate =>
      (Selection.reuse retained same accurate).resolveWith interval start_le point_le_finish ()
  | .request previous =>
      let state := (source point).request previous request.tolerance request.positive
      let reading := (source point).bound state
      (Selection.request previous).resolveWith interval start_le point_le_finish ⟨⟨state, rfl⟩, ⟨reading, rfl⟩⟩

/-- Any certified returned state and readback assemble to the original selected observation. -/
theorem resolveWith_eq_resolve {source : Fraction.Rational → BoundProcess} {point : Fraction.Rational}
    {request : AccuracyRequest} (selection : Selection source point request) (interval : Partition.Interval)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (reply : selection.Reply) :
    selection.resolveWith interval start_le point_le_finish reply =
      selection.resolve interval start_le point_le_finish := by
  cases selection with
  | reuse retained same accurate =>
      cases reply
      rfl
  | request previous =>
      rcases reply with ⟨⟨state, stateEq⟩, ⟨reading, readingEq⟩⟩
      cases stateEq
      cases readingEq
      rfl

end Selection

/-- Decide whether to reuse one saved point or request the exact same-tag or initial predecessor. -/
@[expose] def selectSaved {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (point : Fraction.Rational) (request : AccuracyRequest) : Selection source point request :=
  if same : point = retained.point then
    if accurate : retained.reading.width < request.tolerance then .reuse retained same accurate
    else .request (retained.previousAt point)
  else .request (retained.previousAt point)

/-- A saved point with the requested tag and width selects its original no-request branch. -/
theorem selectSaved_reuse {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (point : Fraction.Rational) (request : AccuracyRequest) (same : point = retained.point)
    (accurate : retained.reading.width < request.tolerance) :
    selectSaved retained point request = .reuse retained same accurate := by
  unfold selectSaved
  rw [dif_pos same, dif_pos accurate]

/-- A matching point with an insufficient reading selects its exact retained predecessor. -/
theorem selectSaved_request {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (point : Fraction.Rational) (request : AccuracyRequest) (same : point = retained.point)
    (inaccurate : ¬ retained.reading.width < request.tolerance) :
    selectSaved retained point request = .request (retained.previousAt point) := by
  unfold selectSaved
  rw [dif_pos same, dif_neg inaccurate]

/-- A changed rational tag selects the initial state of that tag's original point process. -/
theorem selectSaved_new_tag {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (point : Fraction.Rational) (request : AccuracyRequest) (different : point ≠ retained.point) :
    selectSaved retained point request = .request (source point).initial := by
  unfold selectSaved previousAt
  rw [dif_neg different, dif_neg different]

/-- Select a sufficient saved or newly requested point observation at the supplied rational tag.

A sufficient same-tag observation is retained directly. A tighter request
continues the saved state; a changed tag starts its own point process. The
returned certificate binds the exact tag and the requested width. -/
@[expose] def select {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (request : AccuracyRequest) :
    {selected : NumericalPoint source // selected.point = point ∧ selected.reading.width < request.tolerance} :=
  let selected := (selectSaved retained point request).resolve interval start_le point_le_finish
  ⟨selected.val, selected.property.2⟩

/-- Transport one original point request along an exact equality of its rational tags. -/
theorem transport_request {source : Fraction.Rational → BoundProcess} {first second : Fraction.Rational}
    (same : first = second) (previous state : (source first).State) (request : AccuracyRequest)
    (state_eq : state = (source first).request previous request.tolerance request.positive) :
    (same ▸ state) = (source second).request (same ▸ previous) request.tolerance request.positive := by
  cases same
  exact state_eq

/-- Transport the retained point readback along the same exact tag equality. -/
theorem transport_reading {source : Fraction.Rational → BoundProcess} {first second : Fraction.Rational}
    (same : first = second) (state : (source first).State) (reading : Purelib.Data.Rat.Interval)
    (reading_eq : reading = (source first).bound state) :
    reading = (source second).bound (same ▸ state) := by
  cases same
  exact reading_eq

/-- Assemble an interval-tagged point from the same selected point observation. -/
@[expose] def fromSelected {source : Fraction.Rational → BoundProcess} (interval : Partition.Interval)
    (point : Fraction.Rational) (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (request : AccuracyRequest)
    (selected : {selected : NumericalPoint source //
      selected.point = point ∧ selected.reading.width < request.tolerance}) : NumericalPoint source := by
  let saved := selected.val
  have same := selected.property.1
  exact
    { interval := interval
      point := point
      start_le := start_le
      point_le_finish := point_le_finish
      previous := same ▸ saved.previous
      request := saved.request
      state := same ▸ saved.state
      state_eq := transport_request same saved.previous saved.state saved.request saved.state_eq
      reading := saved.reading
      reading_eq := transport_reading same saved.state saved.reading saved.reading_eq }

/-- Reassembling a resolved branch retains its exact returned numerical point. -/
theorem fromSelected_resolve {source : Fraction.Rational → BoundProcess} {point : Fraction.Rational}
    {request : AccuracyRequest} (selection : Selection source point request) (interval : Partition.Interval)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish) :
    let selected := selection.resolve interval start_le point_le_finish
    fromSelected interval point start_le point_le_finish request ⟨selected.val, selected.property.2⟩ =
      selected.val := by
  cases selection with
  | reuse retained same accurate =>
      cases same
      rfl
  | request previous => rfl

/-- Read the selected point on the supplied interval, retaining the displayed rational tag.

The actual observation is selected once and its original state and reading
are consumed directly. Assembly transports only their tag identity; it does
not repeat a point request. -/
@[expose] def retag {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (request : AccuracyRequest) : NumericalPoint source :=
  fromSelected interval point start_le point_le_finish request
    (retained.select interval point start_le point_le_finish request)

/-- Resolving the shared saved-point decision gives the exact original retagged point. -/
theorem selectSaved_resolve_eq_retag {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish) (request : AccuracyRequest) :
    ((selectSaved retained point request).resolve interval start_le point_le_finish).val =
      retained.retag interval point start_le point_le_finish request := by
  unfold retag select
  exact (fromSelected_resolve (selectSaved retained point request) interval start_le point_le_finish).symm

/-- A sufficient reading at the original tag is moved without requesting the point process again. -/
theorem retag_reused_at_point {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (start_le : interval.start ≤ retained.point)
    (point_le_finish : retained.point ≤ interval.finish) (request : AccuracyRequest)
    (accurate : retained.reading.width < request.tolerance) :
    retained.retag interval retained.point start_le point_le_finish request =
      retained.move interval retained.point start_le point_le_finish rfl := by
  rw [← selectSaved_resolve_eq_retag]
  rw [selectSaved_reuse retained retained.point request rfl accurate]
  rfl

/-- A sufficient reading at an equal rational tag is moved without another point request. -/
theorem retag_reused_of_eq {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational) (start_le : interval.start ≤ point)
    (point_le_finish : point ≤ interval.finish) (request : AccuracyRequest) (same : point = retained.point)
    (accurate : retained.reading.width < request.tolerance) :
    retained.retag interval point start_le point_le_finish request =
      retained.move interval point start_le point_le_finish same := by
  cases same
  exact retained.retag_reused_at_point interval start_le point_le_finish request accurate

/-- An insufficient reading at the original tag continues from the exact saved point state. -/
theorem retag_refines_at_point_of_not_accurate {source : Fraction.Rational → BoundProcess}
    (retained : NumericalPoint source) (interval : Partition.Interval) (start_le : interval.start ≤ retained.point)
    (point_le_finish : retained.point ≤ interval.finish) (request : AccuracyRequest)
    (notAccurate : ¬ retained.reading.width < request.tolerance) :
    retained.retag interval retained.point start_le point_le_finish request =
      observe source interval retained.point start_le point_le_finish retained.state request := by
  rw [← selectSaved_resolve_eq_retag]
  rw [selectSaved_request retained retained.point request rfl notAccurate]
  rw [retained.previousAt_point]
  rfl

/-- Every retagged reading meets the supplied request, including the saved-reading branch. -/
theorem retag_reading_width_lt {source : Fraction.Rational → BoundProcess} (retained : NumericalPoint source)
    (interval : Partition.Interval) (point : Fraction.Rational) (start_le : interval.start ≤ point)
    (point_le_finish : point ≤ interval.finish) (request : AccuracyRequest) :
    (retained.retag interval point start_le point_le_finish request).reading.width < request.tolerance :=
  (retained.select interval point start_le point_le_finish request).property.2

/-- Find the first saved observation at the tag that already satisfies the supplied point request. -/
@[expose] def findSufficient {source : Fraction.Rational → BoundProcess} :
    List (NumericalPoint source) → (point : Fraction.Rational) → (request : AccuracyRequest) →
      Option {retained : NumericalPoint source // retained.point = point ∧ retained.reading.width < request.tolerance}
  | [], _, _ => none
  | retained :: remaining, point, request =>
      if same : retained.point = point then
        if accurate : retained.reading.width < request.tolerance then
          some ⟨retained, same, accurate⟩
        else
          findSufficient remaining point request
      else
        findSufficient remaining point request

/-- Find the first saved observation owned by the supplied rational tag. -/
@[expose] def findTag {source : Fraction.Rational → BoundProcess} :
    List (NumericalPoint source) → (point : Fraction.Rational) →
      Option {retained : NumericalPoint source // retained.point = point}
  | [], _ => none
  | retained :: remaining, point =>
      if same : retained.point = point then some ⟨retained, same⟩ else findTag remaining point

/-- A sufficient matching first point is selected from the original numerical bank. -/
theorem findSufficient_head {source : Fraction.Rational → BoundProcess}
    (retained : NumericalPoint source) (remaining : List (NumericalPoint source))
    (point : Fraction.Rational) (request : AccuracyRequest) (same : retained.point = point)
    (accurate : retained.reading.width < request.tolerance) :
    findSufficient (retained :: remaining) point request = some ⟨retained, same, accurate⟩ := by
  change (if same : retained.point = point then
    if accurate : retained.reading.width < request.tolerance then some ⟨retained, same, accurate⟩
    else findSufficient remaining point request else findSufficient remaining point request) = _
  rw [dif_pos same, dif_pos accurate]

/-- A matching first point is selected for continuation when no sufficient point was found. -/
theorem findTag_head {source : Fraction.Rational → BoundProcess}
    (retained : NumericalPoint source) (remaining : List (NumericalPoint source))
    (point : Fraction.Rational) (same : retained.point = point) :
    findTag (retained :: remaining) point = some ⟨retained, same⟩ := by
  change (if same : retained.point = point then some ⟨retained, same⟩ else findTag remaining point) = _
  rw [dif_pos same]

/-- Select the first sufficient saved point, or the first saved point at the original tag. -/
@[expose] def bankCandidate {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (point : Fraction.Rational) (request : AccuracyRequest) : Option (NumericalPoint source) :=
  match findSufficient cached point request with
  | some retained => some retained.val
  | none => (findTag cached point).map Subtype.val

/-- Decide the actual reuse or predecessor request selected from the original point bank. -/
@[expose] def selectBank (source : Fraction.Rational → BoundProcess) (cached : List (NumericalPoint source))
    (point : Fraction.Rational) (request : AccuracyRequest) : Selection source point request :=
  match bankCandidate cached point request with
  | some retained => selectSaved retained point request
  | none => .request (source point).initial

/-- The original first sufficient bank entry selects the exact saved observation. -/
theorem selectBank_sufficient {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (point : Fraction.Rational) (request : AccuracyRequest)
    (retained : {pointData : NumericalPoint source // pointData.point = point ∧
      pointData.reading.width < request.tolerance})
    (found : findSufficient cached point request = some retained) :
    selectBank source cached point request = .reuse retained.val retained.property.1.symm retained.property.2 := by
  unfold selectBank bankCandidate
  rw [found]
  exact selectSaved_reuse retained.val point request retained.property.1.symm retained.property.2

/-- With no sufficient entry, an insufficient same-tag entry supplies its actual saved predecessor. -/
theorem selectBank_saved {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (point : Fraction.Rational) (request : AccuracyRequest)
    (retained : {pointData : NumericalPoint source // pointData.point = point})
    (noneSufficient : findSufficient cached point request = none) (found : findTag cached point = some retained)
    (inaccurate : ¬ retained.val.reading.width < request.tolerance) :
    selectBank source cached point request = .request (retained.val.previousAt point) := by
  unfold selectBank bankCandidate
  rw [noneSufficient, found]
  exact selectSaved_request retained.val point request retained.property.symm inaccurate

/-- With no saved point at the tag, the original point process starts at its initial state. -/
theorem selectBank_initial {source : Fraction.Rational → BoundProcess} (cached : List (NumericalPoint source))
    (point : Fraction.Rational) (request : AccuracyRequest)
    (noneSufficient : findSufficient cached point request = none) (noneTag : findTag cached point = none) :
    selectBank source cached point request = .request (source point).initial := by
  unfold selectBank bankCandidate
  rw [noneSufficient, noneTag]
  rfl

/-- Read a rational point from the retained bank, continuing a matching state only if needed.

An already sufficient matching observation takes precedence over a wider one.
If no saved observation has the tag, the original point process starts from
its initial state. Every returned point remains owned by the same source. -/
@[expose] def atCached (source : Fraction.Rational → BoundProcess) (cached : List (NumericalPoint source))
    (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish)
    (request : AccuracyRequest) : Observation source interval point request :=
  (selectBank source cached point request).resolve interval start_le point_le_finish

/-- Certified point replies assemble to the exact original cache-selected observation. -/
theorem selectBank_resolveWith_eq_atCached (source : Fraction.Rational → BoundProcess)
    (cached : List (NumericalPoint source)) (interval : Partition.Interval) (point : Fraction.Rational)
    (start_le : interval.start ≤ point) (point_le_finish : point ≤ interval.finish) (request : AccuracyRequest)
    (reply : (selectBank source cached point request).Reply) :
    (selectBank source cached point request).resolveWith interval start_le point_le_finish reply =
      atCached source cached interval point start_le point_le_finish request :=
  Selection.resolveWith_eq_resolve _ interval start_le point_le_finish reply

/-- Read an interval start from the retained point bank. -/
@[expose] def atStartCached (source : Fraction.Rational → BoundProcess)
    (cached : List (NumericalPoint source)) (interval : Partition.Interval)
    (valid : interval.Valid) (request : AccuracyRequest) : StartObservation source interval request :=
  atCached source cached interval interval.start le_rfl valid.2.1.le request

/-- A sufficient saved point selected by the bank is the exact point used by interval-start construction. -/
theorem atStartCached_of_sufficient {source : Fraction.Rational → BoundProcess}
    (cached : List (NumericalPoint source)) (interval : Partition.Interval) (valid : interval.Valid)
    (request : AccuracyRequest)
    (retained : {point : NumericalPoint source // point.point = interval.start ∧
      point.reading.width < request.tolerance})
    (found : findSufficient cached interval.start request = some retained) :
    (atStartCached source cached interval valid request).val =
      retained.val.retag interval interval.start le_rfl valid.2.1.le request := by
  unfold atStartCached atCached selectBank bankCandidate
  rw [found]
  exact selectSaved_resolve_eq_retag retained.val interval interval.start le_rfl valid.2.1.le request

/-- With no sufficient saved point, interval-start construction retags the selected matching point. -/
theorem atStartCached_of_tag {source : Fraction.Rational → BoundProcess}
    (cached : List (NumericalPoint source)) (interval : Partition.Interval) (valid : interval.Valid)
    (request : AccuracyRequest) (retained : {point : NumericalPoint source // point.point = interval.start})
    (noneSufficient : findSufficient cached interval.start request = none)
    (found : findTag cached interval.start = some retained) :
    (atStartCached source cached interval valid request).val =
      retained.val.retag interval interval.start le_rfl valid.2.1.le request := by
  unfold atStartCached atCached selectBank bankCandidate
  rw [noneSufficient, found]
  exact selectSaved_resolve_eq_retag retained.val interval interval.start le_rfl valid.2.1.le request

/-- Refining a point request narrows the exact cached reading of the saved state. -/
theorem refine_reading {source : Fraction.Rational → BoundProcess}
    (retained : NumericalPoint source) (request : AccuracyRequest) :
    Purelib.Data.Rat.Interval.Refines (retained.refine request).reading retained.reading := by
  rw [retained.reading_eq]
  exact (source retained.point).request_refines retained.state request.tolerance request.positive

end NumericalPoint

set_option genInjectivity false in
/-- A numerical source frontier with pointwise admission of all original finite point states.

The partition, ordered cells and exact lengths are retained. At every
rational point in a cell, that cell's range overlaps every displayed state of
the original point process. This is finite joint admission, not selection of
an exact point value or an assumption of source-free replay. -/
structure NumericalFrontier (source : Fraction.Rational → BoundProcess) where
  /-- The original normalized unit partition. -/ partition : Unit.Normalized
  /-- The ordered numerical tags, cached replies and rational cell ranges. -/
  cells : List (IntegrationCell (NumericalPoint source))
  /-- The cell domains are the original ordered partition intervals. -/ domains_eq :
    cells.map (fun cell => cell.item.interval) = partition.intervals
  /-- Every original cell weight is its exact rational domain length. -/ weight_eq :
    ∀ cell ∈ cells, cell.weight = cell.item.interval.signedLength
  /-- Each cell range overlaps every finite source state at every rational point in its domain. -/ source_overlap :
    ∀ cell ∈ cells, ∀ point, cell.item.interval.start ≤ point → point ≤ cell.item.interval.finish →
      ∀ state : (source point).State,
        cell.lower ≤ ((source point).bound state).upper ∧ ((source point).bound state).lower ≤ cell.upper

constructive_injectivity NumericalFrontier

namespace NumericalFrontier

/-- Two numerical frontiers with the same partition and ordered cells are equal. -/
theorem ext {source : Fraction.Rational → BoundProcess} (left right : NumericalFrontier source)
    (partition_eq : left.partition = right.partition) (cells_eq : left.cells = right.cells) : left = right := by
  cases left with
  | mk leftPartition leftCells leftDomains leftWeights leftOverlap =>
    cases right with
    | mk rightPartition rightCells rightDomains rightWeights rightOverlap =>
      cases partition_eq
      cases cells_eq
      rfl

/-- Every legal point reading is enclosed after adding its actual observation width.

Pointwise admission gives an overlap between the retained cell range and the
original point-process interval. Inflating by that displayed interval's
width contains every rational reading admitted by the same actual state. -/
theorem source_bounds_with_uncertainty {source : Fraction.Rational → BoundProcess}
    (frontier : NumericalFrontier source) (cell : IntegrationCell (NumericalPoint source))
    (member : cell ∈ frontier.cells) (point : Fraction.Rational)
    (lower : cell.item.interval.start ≤ point) (upper : point ≤ cell.item.interval.finish)
    (state : (source point).State) (reading : Fraction.Rational)
    (inside : ((source point).bound state).Contains reading) :
    cell.lower - ((source point).bound state).width ≤ reading ∧
      reading ≤ cell.upper + ((source point).bound state).width := by
  let observation := (source point).bound state
  have overlap := frontier.source_overlap cell member point lower upper state
  have lowerBound := Fraction.Order.Arithmetic.sub_le_sub_right_direct overlap.1 observation.width
  have lowerIdentity : observation.upper - observation.width = observation.lower := by
    dsimp [Purelib.Data.Rat.Interval.width]
    ring1
  rw [lowerIdentity] at lowerBound
  have upperBound := Fraction.Order.Arithmetic.add_le_add_right_direct overlap.2 observation.width
  have upperIdentity : observation.lower + observation.width = observation.upper := by
    dsimp [Purelib.Data.Rat.Interval.width]
    ring1
  rw [upperIdentity] at upperBound
  exact ⟨lowerBound.trans inside.1, inside.2.trans upperBound⟩

/-- Build one cell from an actual numerical request and its reading-derived range. -/
@[expose] def rangeCell (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (entry : {interval // interval ∈ partition.intervals}) : IntegrationCell (NumericalPoint source) :=
  let tag := NumericalPoint.atStart source entry.val (partition.valid entry.val entry.property) request
  let bound := range tag
  { item := tag
    weight := entry.val.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos (partition.valid entry.val entry.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- Build a cell from one supplied interval-start observation and its derived range. -/
@[expose] def selectedRangeCell (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (selected : (entry : {interval // interval ∈ partition.intervals}) →
      NumericalPoint.StartObservation source entry.val request)
    (entry : {interval // interval ∈ partition.intervals}) : IntegrationCell (NumericalPoint source) :=
  let tag := (selected entry).val
  let bound := range tag
  { item := tag
    weight := entry.val.signedLength
    weight_nonnegative := (Partition.Interval.signedLength_pos (partition.valid entry.val entry.property)).le
    lower := bound.lower
    upper := bound.upper
    range_valid := bound.valid }

/-- Build a numerical frontier from the supplied actual point observations and their source-admission law. -/
@[expose] def ofSelectedRanges (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (selected : (entry : {interval // interval ∈ partition.intervals}) →
      NumericalPoint.StartObservation source entry.val request)
    (range_overlap : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
      ∀ state : (source point).State,
        (range (selected ⟨interval, member⟩).val).Overlaps ((source point).bound state)) :
    NumericalFrontier source := by
  let makeCell := selectedRangeCell source partition request range selected
  let cells := partition.intervals.attach.map makeCell
  exact
    { partition := partition
      cells := cells
      domains_eq := by
        change (partition.intervals.attach.map makeCell).map (fun cell => cell.item.interval) = partition.intervals
        rw [Purelib.Data.List.Map.map_map]
        calc
          _ = partition.intervals.attach.map Subtype.val := by
            apply Purelib.Data.List.Map.map_congr_left
            intro entry _
            exact (selected entry).property.1
          _ = partition.intervals := Purelib.Data.List.attach_map_subtype_val _
      weight_eq := by
        intro cell member
        change cell ∈ partition.intervals.attach.map makeCell at member
        obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
        cases equal
        change entry.val.signedLength = (selected entry).val.interval.signedLength
        rw [(selected entry).property.1]
      source_overlap := by
        intro cell member point lower upper state
        change cell ∈ partition.intervals.attach.map makeCell at member
        obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
        cases equal
        change (selected entry).val.interval.start ≤ point at lower
        change point ≤ (selected entry).val.interval.finish at upper
        rw [(selected entry).property.1] at lower upper
        exact range_overlap entry.val entry.property point lower upper state }

/-- Every selected frontier cell retains an observation meeting the original point-width request. -/
theorem ofSelectedRanges_reading_width_lt (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (selected : (entry : {interval // interval ∈ partition.intervals}) →
      NumericalPoint.StartObservation source entry.val request)
    (range_overlap : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
      ∀ state : (source point).State,
        (range (selected ⟨interval, member⟩).val).Overlaps ((source point).bound state))
    (cell : IntegrationCell (NumericalPoint source))
    (member : cell ∈ (ofSelectedRanges source partition request range selected range_overlap).cells) :
    cell.item.reading.width < request.tolerance := by
  change cell ∈ partition.intervals.attach.map (selectedRangeCell source partition request range selected) at member
  obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  exact (selected entry).property.2.2

/-- A selected cell's oscillation is the width of its actual reading-derived range. -/
theorem ofSelectedRanges_oscillation (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (selected : (entry : {interval // interval ∈ partition.intervals}) →
      NumericalPoint.StartObservation source entry.val request)
    (range_overlap : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
      ∀ state : (source point).State,
        (range (selected ⟨interval, member⟩).val).Overlaps ((source point).bound state))
    (cell : IntegrationCell (NumericalPoint source))
    (member : cell ∈ (ofSelectedRanges source partition request range selected range_overlap).cells) :
    cell.oscillation = (range cell.item).width := by
  change cell ∈ partition.intervals.attach.map (selectedRangeCell source partition request range selected) at member
  obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  rfl

/-- A fresh point request supplies an interval-start observation with its requested width. -/
@[expose] def freshStart (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (entry : {interval // interval ∈ partition.intervals}) :
    NumericalPoint.StartObservation source entry.val request :=
  let tag := NumericalPoint.atStart source entry.val (partition.valid entry.val entry.property) request
  ⟨tag, rfl, rfl, tag.reading_width_lt⟩

/-- Build a numerical frontier from actual requested point intervals and their source-admission law.

Every original partition interval is read at its start with the supplied
positive request. The range law applies to all rational points in each
closed cell and every state of the original point process. -/
@[expose] def ofRanges (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (range_overlap : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
      ∀ state : (source point).State,
        (range (NumericalPoint.atStart source interval (partition.valid interval member) request)).Overlaps
          ((source point).bound state)) : NumericalFrontier source :=
  ofSelectedRanges source partition request range (freshStart source partition request) range_overlap

/-- The constructed cell's oscillation is the width of its actual reading-derived range. -/
theorem ofRanges_oscillation (source : Fraction.Rational → BoundProcess) (partition : Unit.Normalized)
    (request : AccuracyRequest) (range : NumericalPoint source → Purelib.Data.Rat.Interval)
    (range_overlap : ∀ (interval : Partition.Interval) (member : interval ∈ partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
      ∀ state : (source point).State,
        (range (NumericalPoint.atStart source interval (partition.valid interval member) request)).Overlaps
          ((source point).bound state))
    (cell : IntegrationCell (NumericalPoint source))
    (member : cell ∈ (ofRanges source partition request range range_overlap).cells) :
    cell.oscillation = (range cell.item).width := by
  change cell ∈ partition.intervals.attach.map (rangeCell source partition request range) at member
  obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  rfl

/-- The exact numerical-cell weights cover the unit interval once. -/
theorem totalWeight {source : Fraction.Rational → BoundProcess} (frontier : NumericalFrontier source) :
    integrationWeight frontier.cells = 1 := by
  rw [integrationWeight_eq_lengthSum (fun point : NumericalPoint source => point.interval)
    frontier.cells frontier.weight_eq, frontier.domains_eq]
  exact frontier.partition.lengthSum

end NumericalFrontier

end Purelib.Integration

end
