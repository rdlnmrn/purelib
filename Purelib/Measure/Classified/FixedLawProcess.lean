module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Bound.Schedule
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Bound.Process
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Classified.Distribution
import Purelib.Measure.Classified.Soundness
import Purelib.Measure.Classified.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Interval.Basic

section
@[expose] public section

/-!
# Sound finite event classifications

A three-way status table becomes a probability enclosure once its inside and
outside claims are certified against one executable event.  Unresolved rows
need no claim; their exact rational weight is the complete error budget.
-/

namespace Purelib.Measure

/-! ## Arbitrarily accurate finite classifications -/

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a refinable classification procedure for one exact distribution and Boolean event.

Every state certifies sound statuses on the original atoms. Positive tolerance requests refine the current statuses and
reduce their unresolved probability below that tolerance, while all states refine the retained initial classification.
-/
structure ClassificationProcess {α : Type}
    (distribution : Distribution α) (event : α → Bool) where
  /-- The retained classification-state carrier. -/ State : Type
  /-- The payload classification read from each exact state. -/ status : State → α → Status
  /-- The retained initial classification state. -/ initial : State
  /-- Refine the supplied state for the exact positive rational tolerance. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- Each state classifies the original distribution and event soundly. -/ sound : ∀ state,
    ClassificationSoundOn distribution.atoms (status state) event
  /-- A requested state's statuses refine those of the exact input state on every original occurrence. -/
    request_refines : ∀ state epsilon positive atom,
    atom ∈ distribution.atoms →
      (status (request state epsilon positive) atom.item).Refines
        (status state atom.item)
  /-- The requested state's unresolved probability is strictly below the same requested tolerance. -/ accurate : ∀ state
    epsilon positive,
    distribution.probability
      (unresolvedStatusEvent (status (request state epsilon positive))) <
        epsilon
  /-- Every retained state refines the original initial statuses on the original distribution atoms. -/ refinesInitial :
    ∀ state atom, atom ∈ distribution.atoms →
    (status state atom.item).Refines (status initial atom.item)

constructive_injectivity ClassificationProcess

namespace ClassificationProcess

section
open Purelib
/-- Read a bound process from the same retained classification states, requests and event intervals.

The exact probability of unresolved status is the interval width, so the original request accuracy and status refinement
certificates supply the bound-process guarantees. -/
def toBoundProcess {α : Type} {distribution : Distribution α}
    {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event) : Approximation.BoundProcess where
  State := process.State
  bound state := eventBound
    (distribution.classifiedEventFrontier (process.status state))
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    distribution.classifiedEventFrontier_refines
      (process.status (process.request state epsilon positive))
      (process.status state)
      (process.request_refines state epsilon positive)
  accurate state epsilon positive := by
    rw [distribution.classifiedEventFrontier_width]
    exact process.accurate state epsilon positive
  refinesInitial state :=
    distribution.classifiedEventFrontier_refines
      (process.status state) (process.status process.initial)
      (process.refinesInitial state)

/-- Every retained classification state encloses the original fixed event probability in its bound interval. -/
theorem probability_mem_bound {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) :
    (process.toBoundProcess.bound state).Contains
      (distribution.probability event) :=
  distribution.probability_mem_classifiedEventFrontier
    (process.status state) event (process.sound state)

end

section
open Purelib
open Purelib.Data.Rat
/-- A positive tolerance request gives a rational approximation strictly within that tolerance of the original event
probability in both directions. -/
theorem probability_close_to_approximation {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    distribution.probability event -
          process.toBoundProcess.approximate state epsilon positive < epsilon ∧
      process.toBoundProcess.approximate state epsilon positive -
          distribution.probability event < epsilon :=
  process.toBoundProcess.candidate_close_to_approximate
    state epsilon positive
    (process.probability_mem_bound
      (process.request state epsilon positive))

/-- The requested bound's exact width is the probability of unresolved status at that same requested state. -/
theorem requested_width_eq_unresolved_probability {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (process.toBoundProcess.bound
      (process.request state epsilon positive)).width =
        distribution.probability
          (unresolvedStatusEvent
            (process.status (process.request state epsilon positive))) :=
  distribution.classifiedEventFrontier_width _

end

open Purelib in
/-- Run the exact finite accuracy-request list through the retained classification state. -/
def runRequests {α : Type} {distribution : Distribution α}
    {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) (requests : List Approximation.AccuracyRequest) : process.State :=
  process.toBoundProcess.runRequests state requests

open Purelib in
open Purelib.Data.Rat in
/-- Read the rational bound approximation after processing the exact retained finite request list. -/
def runRequestsApproximation {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) (requests : List Approximation.AccuracyRequest) : Fraction.Rational :=
  process.toBoundProcess.runRequestsApproximation state requests

open Purelib
/-- After all finite requests, unresolved probability is below every tolerance occurring in that exact request list. -/
theorem runRequests_unresolved_probability_lt_of_mem {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) (requests : List Approximation.AccuracyRequest)
    (request : Approximation.AccuracyRequest) (member : request ∈ requests) :
    distribution.probability
        (unresolvedStatusEvent
          (process.status (process.runRequests state requests))) <
      request.tolerance := by
  have accurate := process.toBoundProcess.runRequests_width_lt_of_mem
    state requests request member
  change (eventBound (distribution.classifiedEventFrontier
    (process.status (process.runRequests state requests)))).width <
      request.tolerance at accurate
  rw [distribution.classifiedEventFrontier_width] at accurate
  exact accurate

/-- The final finite-request approximation is strictly within each retained request tolerance of the original event
probability. -/
theorem runRequests_probability_close_to_approximation_of_mem {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : Measure.ClassificationProcess distribution event)
    (state : process.State) (requests : List Approximation.AccuracyRequest)
    (request : Approximation.AccuracyRequest) (member : request ∈ requests) :
    distribution.probability event -
          process.runRequestsApproximation state requests <
        request.tolerance ∧
      process.runRequestsApproximation state requests -
          distribution.probability event < request.tolerance := by
  exact process.toBoundProcess
    |>.runRequests_candidate_close_to_approximation_of_mem
      state requests request member
      (process.probability_mem_bound
        (process.runRequests state requests))

end ClassificationProcess

end Purelib.Measure

end
