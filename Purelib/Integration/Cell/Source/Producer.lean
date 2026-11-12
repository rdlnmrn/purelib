module
public import Purelib.Integration.Cell.Source.Comparison.Split
public import Purelib.Integration.Cell.Controller
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Persistent finite source-frontier producers

A producer computes a source-linked frontier for each positive request and
retains its own result data. Continuing a saved frontier intersects the
actual source ranges on a common partition and records the original certified
cell splits. Concrete producers must establish their own accuracy laws.
-/

public section

namespace Purelib.Integration.SourceFrontier

open Purelib.Approximation
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A finite-accuracy source-frontier producer with its original result type.

Every positive request computes an actual retained result and a source-linked
frontier meeting that request. This interface alone does not certify that an
arbitrary callback is finite source code; concrete constructions supply that. -/
structure Producer (source : Fraction.Rational → Fraction.Rational) where
  /-- The producer's retained result data for one request. -/ Output : Type
  /-- Compute the original result for a positive rational request. -/ request : AccuracyRequest → Output
  /-- Compute the same original result while reusing matching retained source readings. -/ requestCached :
    List (SourcePoint source) → AccuracyRequest → Output
  /-- Cache selection preserves the original complete result. -/ requestCached_eq : ∀ cached demand,
    requestCached cached demand = request demand
  /-- Read the source-linked frontier from the actual result. -/ frontier : Output → SourceFrontier source
  /-- The actual computed frontier meets the original request's width. -/ accurate : ∀ demand,
    (integralBound (frontier (request demand)).cells).width < demand.tolerance

constructive_injectivity Producer

namespace Producer

/-- Combine the supplied source bank with the exact points of the saved frontier.

The supplied bank keeps its original precedence. The frontier's points remain
available when no earlier supplied observation has the same rational tag. -/
@[expose] def effectiveBank {source : Fraction.Rational → Fraction.Rational}
    (previous : SourceFrontier source) (cached : List (SourcePoint source)) : List (SourcePoint source) :=
  cached ++ previous.cells.map (fun cell => cell.item)

set_option genInjectivity false in
/-- A saved frontier either already meets the request or is refined using one fresh producer result.

The reused branch retains the exact saved frontier without running the
producer. The refined branch retains the original producer output and common
observations used to construct its split frontier. -/
inductive Continuation {source : Fraction.Rational → Fraction.Rational} (producer : Producer source)
    (previous : SourceFrontier source) where
  /-- The saved frontier already meets the request. -/ | reused (request : AccuracyRequest)
      (accurate : (integralBound previous.cells).width < request.tolerance)
  /-- The cache-aware result and its actual common observations refine the saved frontier. -/ | refined
      (request : AccuracyRequest) (cached : List (SourcePoint source)) (fresh : producer.Output)
      (fresh_eq : fresh = producer.requestCached (effectiveBank previous cached) request)
      (common : CommonReadings previous (producer.frontier fresh))
      (split : IntegrationFrontierRefines common.intersection.cells previous.cells)

constructive_injectivity Continuation

namespace Continuation

/-- The exact original request retained by either continuation branch. -/
@[expose] def request {source : Fraction.Rational → Fraction.Rational} {producer : Producer source}
    {previous : SourceFrontier source} : Continuation producer previous → AccuracyRequest
  | .reused request _ => request
  | .refined request _ _ _ _ _ => request

/-- The retained saved frontier or the actual fresh/common intersection. -/
@[expose] def frontier {source : Fraction.Rational → Fraction.Rational} {producer : Producer source}
    {previous : SourceFrontier source} : Continuation producer previous → SourceFrontier source
  | .reused _ _ => previous
  | .refined _ _ _ _ common _ => common.intersection

/-- Either continuation branch is a finite split refinement of the saved frontier. -/
theorem split_refines {source : Fraction.Rational → Fraction.Rational} {producer : Producer source}
    {previous : SourceFrontier source} (continuation : Continuation producer previous) :
    IntegrationFrontierRefines continuation.frontier.cells previous.cells := by
  cases continuation with
  | reused _ _ => exact .refl _
  | refined _ _ _ _ _ split => exact split

/-- The resulting integral enclosure refines the exact saved frontier's enclosure. -/
theorem refines_previous {source : Fraction.Rational → Fraction.Rational} {producer : Producer source}
    {previous : SourceFrontier source} (continuation : Continuation producer previous) :
    Purelib.Data.Rat.Interval.Refines (integralBound continuation.frontier.cells) (integralBound previous.cells) :=
  continuation.split_refines.integralBound_refines

/-- Each actual continuation meets its retained original request. -/
theorem accurate {source : Fraction.Rational → Fraction.Rational} {producer : Producer source}
    {previous : SourceFrontier source} (continuation : Continuation producer previous) :
    (integralBound continuation.frontier.cells).width < continuation.request.tolerance := by
  cases continuation with
  | reused _ accurate => exact accurate
  | refined request cached fresh fresh_eq common _ =>
      have freshAccurate : (integralBound (producer.frontier fresh).cells).width < request.tolerance := by
        rw [fresh_eq]
        rw [producer.requestCached_eq]
        exact producer.accurate request
      exact common.intersection_refines_right.width_le.trans_lt freshAccurate

end Continuation

/-- Continue a saved frontier with a bank supplied only when further construction is needed.

The accuracy test precedes evaluating the supplied bank, so an already
accurate frontier does not traverse its saved observation history. -/
@[expose] def advanceWithBank {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (readBank : Unit → List (SourcePoint source))
    (previous : SourceFrontier source) (request : AccuracyRequest) :
    Continuation producer previous :=
  if accurate : (integralBound previous.cells).width < request.tolerance then
    .reused request accurate
  else
    let cached := readBank ()
    let bank := effectiveBank previous cached
    let fresh := producer.requestCached bank request
    let available := (producer.frontier fresh).cells.map (fun cell => cell.item) ++
      previous.cells.map (fun cell => cell.item) ++ bank
    let common := SourceFrontier.commonReadingsCached previous (producer.frontier fresh) available
    have split : IntegrationFrontierRefines common.intersection.cells previous.cells := by
      change IntegrationFrontierRefines
        (SourceFrontier.commonReadingsCached previous (producer.frontier fresh) available).intersection.cells
        previous.cells
      rw [SourceFrontier.commonReadingsCached_eq]
      exact CommonReadings.commonReadings_intersection_refines previous (producer.frontier fresh)
    .refined request cached fresh rfl common split

/-- Continue a saved frontier using retained source readings when further construction is needed. -/
@[expose] def advanceCached {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (cached : List (SourcePoint source))
    (previous : SourceFrontier source) (request : AccuracyRequest) :
    Continuation producer previous :=
  advanceWithBank producer (fun _ => cached) previous request

/-- Continue a saved frontier without an additional bank of earlier readings. -/
@[expose] def advance {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (previous : SourceFrontier source) (request : AccuracyRequest) :
    Continuation producer previous :=
  advanceCached producer [] previous request

/-- A satisfied request takes the saved-frontier branch without invoking the producer. -/
theorem advance_reused {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (previous : SourceFrontier source) (request : AccuracyRequest)
    (accurate : (integralBound previous.cells).width < request.tolerance) :
    advance producer previous request = .reused request accurate := by
  unfold advance advanceCached advanceWithBank
  rw [dif_pos accurate]

/-- The continuation retains exactly the supplied request. -/
theorem advance_request {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (previous : SourceFrontier source) (request : AccuracyRequest) :
    (advance producer previous request).request = request := by
  unfold advance advanceCached advanceWithBank
  split <;> rfl

/-- Cache-aware continuation retains exactly the supplied request. -/
theorem advanceCached_request {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (cached : List (SourcePoint source))
    (previous : SourceFrontier source) (request : AccuracyRequest) :
    (advanceCached producer cached previous request).request = request := by
  unfold advanceCached advanceWithBank
  split <;> rfl

/-- A satisfied request leaves any supplied observation-bank computation unevaluated. -/
theorem advanceWithBank_reused {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (readBank : Unit → List (SourcePoint source))
    (previous : SourceFrontier source) (request : AccuracyRequest)
    (accurate : (integralBound previous.cells).width < request.tolerance) :
    advanceWithBank producer readBank previous request = .reused request accurate := by
  unfold advanceWithBank
  rw [dif_pos accurate]

/-- Continuation with a deferred bank retains exactly the supplied request. -/
theorem advanceWithBank_request {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (readBank : Unit → List (SourcePoint source))
    (previous : SourceFrontier source) (request : AccuracyRequest) :
    (advanceWithBank producer readBank previous request).request = request := by
  unfold advanceWithBank
  split <;> rfl

/-- Retain the actual source continuations in the shared finite history controller. -/
@[expose] def controller {source : Fraction.Rational → Fraction.Rational} (producer : Producer source) :
    RefiningController (SourceFrontier source) (SourcePoint source) SourceFrontier.cells where
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
@[expose] def retainedReadingsAt {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (actual : SourceFrontier source) {frontier : SourceFrontier source} :
    producer.controller.History producer.controller.origin frontier → actual = frontier → List (SourcePoint source)
  | .initial, _ => actual.cells.map (fun cell => cell.item)
  | .next history step, _ =>
      step.frontier.cells.map (fun cell => cell.item) ++
        (match step with
        | .reused _ _ => []
        | .refined _ _ fresh _ _ _ => (producer.frontier fresh).cells.map (fun cell => cell.item)) ++
          retainedReadingsAt producer _ history rfl

/-- Collect the exact source observations retained by the original finite continuation history.

Each original producer result and each resulting common frontier remains in
the bank, including observations absent from a later partition. The most
recent retained readings take precedence when rational tags recur. -/
@[expose] def retainedReadings {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) {frontier : SourceFrontier source}
    (history : producer.controller.History producer.controller.origin frontier) : List (SourcePoint source) :=
  retainedReadingsAt producer frontier history rfl

/-- The initial history reads the actual indexed frontier's points in cell order. -/
theorem retainedReadingsAt_initial {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) (actual : SourceFrontier source)
    (same : actual = producer.frontier producer.controller.origin) :
    producer.retainedReadingsAt actual .initial same = actual.cells.map (fun cell => cell.item) := rfl

/-- A next history retains its resulting frontier, fresh output and original predecessor bank in order.

A reused step adds no fresh output; a refined step retains the points of its
actual saved producer output before the predecessor's observations. -/
theorem retainedReadings_next {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) {previous : SourceFrontier source}
    (history : producer.controller.History producer.controller.origin previous)
    (step : producer.Continuation previous) :
    producer.retainedReadings (.next history step) =
      step.frontier.cells.map (fun cell => cell.item) ++
        (match step with
        | .reused _ _ => []
        | .refined _ _ fresh _ _ _ => (producer.frontier fresh).cells.map (fun cell => cell.item)) ++
          producer.retainedReadings history := by
  cases step <;> rfl

/-- Construct the original integration process from actual saved source continuations. -/
@[expose] def integrationProcess {source : Fraction.Rational → Fraction.Rational}
    (producer : Producer source) : IntegrationProcess (SourcePoint source) :=
  producer.controller.integrationProcessWith
    (fun state request => producer.advanceWithBank (fun _ => producer.retainedReadings state.2) state.1 request)
    (fun state request => producer.advanceWithBank_request (fun _ => producer.retainedReadings state.2) state.1 request)

/-- Read the same persistent integration process as its original rational bound process. -/
@[expose] def boundProcess {source : Fraction.Rational → Fraction.Rational} (producer : Producer source) :
    BoundProcess := producer.integrationProcess.toBoundProcess

end Producer

end Purelib.Integration.SourceFrontier

end
