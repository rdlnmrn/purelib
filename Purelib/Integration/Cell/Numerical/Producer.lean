module
public import Purelib.Integration.Cell.Numerical.Common.Split
public import Purelib.Integration.Cell.Controller
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Persistent numerical source-frontier producers

Each continuation retains its original producer result, both actual point
request histories and their intersected common frontier. The shared finite
history controller records the original cell splits and positive requests.
-/

public section

namespace Purelib.Integration.NumericalFrontier

open Purelib.Approximation
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A finite-accuracy numerical source producer with its original result type.

Every positive request computes an actual numerical frontier meeting that
request. Concrete builders establish this contract from their own source and
variation data; the interface alone does not certify arbitrary callback code. -/
structure Producer (source : Fraction.Rational → BoundProcess) where
  /-- The original retained result for one request. -/ Output : Type
  /-- Compute an actual original result for a positive request. -/ request : AccuracyRequest → Output
  /-- Read the numerical source frontier from that retained result. -/ frontier : Output → NumericalFrontier source
  /-- The computed original frontier meets the requested width. -/ accurate : ∀ demand,
    (integralBound (frontier (request demand)).cells).width < demand.tolerance
  /-- The original producer's result type for a request with retained point observations. -/ CachedOutput : Type
  /-- Compute a numerical result from the supplied original point observations. -/ requestCached :
    List (NumericalPoint source) → AccuracyRequest → CachedOutput
  /-- Read the actual numerical frontier from the cache-aware result. -/ cachedFrontier :
    CachedOutput → NumericalFrontier source
  /-- The actual cache-aware frontier meets the supplied positive width request. -/ cachedAccurate : ∀ cached demand,
    (integralBound (cachedFrontier (requestCached cached demand)).cells).width < demand.tolerance

constructive_injectivity Producer

namespace Producer

/-- Combine the supplied point bank with the exact points of the saved frontier.

The supplied bank keeps its original precedence. The frontier's point states
remain available when a request revisits their rational tags. -/
@[expose] def effectiveBank {source : Fraction.Rational → BoundProcess}
    (previous : NumericalFrontier source) (cached : List (NumericalPoint source)) : List (NumericalPoint source) :=
  cached ++ previous.cells.map (fun cell => cell.item)

set_option genInjectivity false in
/-- A saved frontier either meets the request or is refined using one cache-aware producer result.

The reused branch retains the exact saved frontier without running the
producer. The refined branch retains the cache-aware producer output and common
observations used to construct its split frontier. -/
inductive Continuation {source : Fraction.Rational → BoundProcess} (producer : Producer source)
    (previous : NumericalFrontier source) where
  /-- The saved frontier already meets the request. -/ | reused (request : AccuracyRequest)
      (accurate : (integralBound previous.cells).width < request.tolerance)
  /-- The cache-aware result and its actual common observations refine the saved frontier. -/ | refined
      (request : AccuracyRequest) (cached : List (NumericalPoint source)) (fresh : producer.CachedOutput)
      (fresh_eq : fresh = producer.requestCached (effectiveBank previous cached) request)
      (common : CommonReadings previous (producer.cachedFrontier fresh) request)
      (split : IntegrationFrontierRefines common.intersection.cells previous.cells)

constructive_injectivity Continuation

namespace Continuation

/-- The exact original request retained by either continuation branch. -/
@[expose] def request {source : Fraction.Rational → BoundProcess} {producer : Producer source}
    {previous : NumericalFrontier source} : Continuation producer previous → AccuracyRequest
  | .reused request _ => request
  | .refined request _ _ _ _ _ => request

/-- The retained saved frontier or the actual fresh/common intersection. -/
@[expose] def frontier {source : Fraction.Rational → BoundProcess} {producer : Producer source}
    {previous : NumericalFrontier source} : Continuation producer previous → NumericalFrontier source
  | .reused _ _ => previous
  | .refined _ _ _ _ common _ => common.intersection

/-- Either continuation branch is a finite split refinement of the saved frontier. -/
theorem split_refines {source : Fraction.Rational → BoundProcess} {producer : Producer source}
    {previous : NumericalFrontier source} (continuation : Continuation producer previous) :
    IntegrationFrontierRefines continuation.frontier.cells previous.cells := by
  cases continuation with
  | reused _ _ => exact .refl _
  | refined _ _ _ _ _ split => exact split

/-- The resulting integral enclosure refines the exact saved frontier's enclosure. -/
theorem refines_previous {source : Fraction.Rational → BoundProcess} {producer : Producer source}
    {previous : NumericalFrontier source} (continuation : Continuation producer previous) :
    Purelib.Data.Rat.Interval.Refines (integralBound continuation.frontier.cells) (integralBound previous.cells) :=
  continuation.split_refines.integralBound_refines

/-- Each actual continuation meets its retained original request. -/
theorem accurate {source : Fraction.Rational → BoundProcess} {producer : Producer source}
    {previous : NumericalFrontier source} (continuation : Continuation producer previous) :
    (integralBound continuation.frontier.cells).width < continuation.request.tolerance := by
  cases continuation with
  | reused _ accurate => exact accurate
  | refined request cached fresh fresh_eq common _ =>
      have freshAccurate : (integralBound (producer.cachedFrontier fresh).cells).width < request.tolerance := by
        rw [fresh_eq]
        exact producer.cachedAccurate (effectiveBank previous cached) request
      exact common.intersection_refines_right.width_le.trans_lt freshAccurate

end Continuation

/-- Continue a saved frontier with a bank supplied only when further construction is needed.

The accuracy test precedes evaluating the supplied bank, so an already
accurate frontier does not traverse its saved observation history. -/
@[expose] def advanceWithBank {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (readBank : Unit → List (NumericalPoint source))
    (previous : NumericalFrontier source) (request : AccuracyRequest) :
    Continuation producer previous :=
  if accurate : (integralBound previous.cells).width < request.tolerance then
    .reused request accurate
  else
    let cached := readBank ()
    let bank := effectiveBank previous cached
    let fresh := producer.requestCached bank request
    let available := (producer.cachedFrontier fresh).cells.map (fun cell => cell.item) ++
      previous.cells.map (fun cell => cell.item) ++ bank
    let common := NumericalFrontier.commonReadingsCached previous (producer.cachedFrontier fresh) available request
    .refined request cached fresh rfl common
      (CommonReadings.commonReadingsCached_intersection_refines previous (producer.cachedFrontier fresh)
        available request)

/-- Continue a saved frontier using its retained point observations when more work is needed. -/
@[expose] def advanceCached {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (cached : List (NumericalPoint source))
    (previous : NumericalFrontier source) (request : AccuracyRequest) :
    Continuation producer previous :=
  advanceWithBank producer (fun _ => cached) previous request

/-- Continue a saved frontier without an additional bank of earlier point observations. -/
@[expose] def advance {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (previous : NumericalFrontier source) (request : AccuracyRequest) :
    Continuation producer previous :=
  advanceCached producer [] previous request

/-- A satisfied request takes the saved-frontier branch without invoking the producer. -/
theorem advance_reused {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (previous : NumericalFrontier source) (request : AccuracyRequest)
    (accurate : (integralBound previous.cells).width < request.tolerance) :
    advance producer previous request = .reused request accurate := by
  unfold advance advanceCached advanceWithBank
  rw [dif_pos accurate]

/-- The continuation retains exactly the supplied request. -/
theorem advance_request {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (previous : NumericalFrontier source) (request : AccuracyRequest) :
    (advance producer previous request).request = request := by
  unfold advance advanceCached advanceWithBank
  split <;> rfl

/-- Cache-aware continuation retains exactly the supplied request. -/
theorem advanceCached_request {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (cached : List (NumericalPoint source))
    (previous : NumericalFrontier source) (request : AccuracyRequest) :
    (advanceCached producer cached previous request).request = request := by
  unfold advanceCached advanceWithBank
  split <;> rfl

/-- A satisfied request leaves any supplied observation-bank computation unevaluated. -/
theorem advanceWithBank_reused {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (readBank : Unit → List (NumericalPoint source))
    (previous : NumericalFrontier source) (request : AccuracyRequest)
    (accurate : (integralBound previous.cells).width < request.tolerance) :
    advanceWithBank producer readBank previous request = .reused request accurate := by
  unfold advanceWithBank
  rw [dif_pos accurate]

/-- Continuation with a deferred bank retains exactly the supplied request. -/
theorem advanceWithBank_request {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (readBank : Unit → List (NumericalPoint source))
    (previous : NumericalFrontier source) (request : AccuracyRequest) :
    (advanceWithBank producer readBank previous request).request = request := by
  unfold advanceWithBank
  split <;> rfl

/-- Retain actual numerical continuations in the shared finite history controller. -/
@[expose] def controller {source : Fraction.Rational → BoundProcess} (producer : Producer source) :
    RefiningController (NumericalFrontier source) (NumericalPoint source) NumericalFrontier.cells where
  Output := producer.Output
  origin := producer.request ⟨1, by decide⟩
  frontier := producer.frontier
  Step := Continuation producer
  next := fun continuation => continuation.frontier
  stepRequest := fun continuation => continuation.request
  advance := advance producer
  advance_request := fun previous request => advance_request producer previous request
  step_refines := fun continuation => continuation.split_refines
  step_accurate := fun continuation => continuation.accurate

/-- Collect a history's readings while carrying its actual indexed frontier.

Each recursive step carries the saved predecessor frontier. The equality
identifies it with the history index, including at the initial frontier. -/
@[expose] def retainedReadingsAt {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (actual : NumericalFrontier source) {frontier : NumericalFrontier source} :
    producer.controller.History producer.controller.origin frontier → actual = frontier → List (NumericalPoint source)
  | .initial, _ => actual.cells.map (fun cell => cell.item)
  | .next history step, _ =>
      (match step with
      | .reused _ _ => []
      | .refined _ _ fresh _ common _ =>
          common.readings.map (fun reading => reading.leftPoint) ++
            common.readings.map (fun reading => reading.rightPoint) ++
            (producer.cachedFrontier fresh).cells.map (fun cell => cell.item)) ++
        retainedReadingsAt producer _ history rfl

/-- Collect the original point observations retained by a finite numerical continuation history.

Both point states from every common observation remain available, even when
only one is used as the next cell's tag. Fresh producer states and the initial
frontier are retained separately, with recent observations first. -/
@[expose] def retainedReadings {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) {frontier : NumericalFrontier source}
    (history : producer.controller.History producer.controller.origin frontier) : List (NumericalPoint source) :=
  retainedReadingsAt producer frontier history rfl

/-- The initial history reads the actual indexed frontier's points in cell order. -/
theorem retainedReadingsAt_initial {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) (actual : NumericalFrontier source)
    (same : actual = producer.frontier producer.controller.origin) :
    producer.retainedReadingsAt actual .initial same = actual.cells.map (fun cell => cell.item) := rfl

/-- A next history retains its actual common point states, fresh output and predecessor bank in order.

A reused step adds no readings; a refined step retains both sides of each
common observation followed by the actual cache-aware producer output. -/
theorem retainedReadings_next {source : Fraction.Rational → BoundProcess}
    (producer : Producer source) {previous : NumericalFrontier source}
    (history : producer.controller.History producer.controller.origin previous)
    (step : producer.Continuation previous) :
    producer.retainedReadings (.next history step) =
      (match step with
      | .reused _ _ => []
      | .refined _ _ fresh _ common _ =>
          common.readings.map (fun reading => reading.leftPoint) ++
            common.readings.map (fun reading => reading.rightPoint) ++
            (producer.cachedFrontier fresh).cells.map (fun cell => cell.item)) ++
        producer.retainedReadings history := by
  cases step <;> rfl

/-- Construct the original integration process from actual saved numerical continuations. -/
@[expose] def integrationProcess {source : Fraction.Rational → BoundProcess} (producer : Producer source) :
    IntegrationProcess (NumericalPoint source) :=
  producer.controller.integrationProcessWith
    (fun state request => producer.advanceWithBank (fun _ => producer.retainedReadings state.2) state.1 request)
    (fun state request => producer.advanceWithBank_request (fun _ => producer.retainedReadings state.2) state.1 request)

/-- Read the same persistent numerical integration process as its original rational bound process. -/
@[expose] def boundProcess {source : Fraction.Rational → BoundProcess} (producer : Producer source) : BoundProcess :=
  producer.integrationProcess.toBoundProcess

end Producer

end Purelib.Integration.NumericalFrontier

end
