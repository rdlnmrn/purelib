module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic

public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

@[expose] public section

/-!
# Finite batches of arbitrary-accuracy requests

This module isolates a useful replacement for an appeal to an infinite
limit: every displayed finite list of positive rational demands has one
explicit final state satisfying all of them.  Preservation comes from finite
refinement, not compactness or a completed intersection.
-/

namespace Purelib.Approximation
namespace BoundProcess

/-- Execute a displayed finite list of requests. -/
def runRequests (process : Purelib.Approximation.BoundProcess) :
    process.State → List Purelib.Approximation.AccuracyRequest → process.State
  | state, [] => state
  | state, request :: remaining =>
      runRequests process
        (process.request state request.tolerance request.positive) remaining

/-- An empty request batch returns the supplied state. -/
@[simp] theorem runRequests_nil (process : Approximation.BoundProcess)
    (state : process.State) : process.runRequests state [] = state := rfl

/-- A nonempty batch executes its first request before the remaining batch. -/
@[simp] theorem runRequests_cons (process : Approximation.BoundProcess)
    (state : process.State) (request : Approximation.AccuracyRequest)
    (remaining : List Approximation.AccuracyRequest) :
    process.runRequests state (request :: remaining) =
      process.runRequests
        (process.request state request.tolerance request.positive) remaining :=
  rfl

/-- The result of any finite request batch refines its starting state. -/
theorem runRequests_refines (process : Approximation.BoundProcess) :
    ∀ (state : process.State) (requests : List Approximation.AccuracyRequest),
      Interval.Refines (process.bound (process.runRequests state requests))
        (process.bound state)
  | _, [] => Refines.refl _
  | state, request :: remaining =>
      (runRequests_refines process
        (process.request state request.tolerance request.positive) remaining).trans
      (process.request_refines state request.tolerance request.positive)

/-- The last state of a finite batch satisfies every demand appearing in the batch, not merely its final demand. -/
theorem runRequests_width_lt_of_mem (process : Approximation.BoundProcess) :
    ∀ (state : process.State) (requests : List Approximation.AccuracyRequest)
      (request : Approximation.AccuracyRequest),
      request ∈ requests →
      (process.bound (process.runRequests state requests)).width <
        request.tolerance
  | state, [], request, member => by
      cases member
  | state, head :: remaining, request, member => by
      cases member with
      | head =>
          exact (runRequests_refines process
            (process.request state head.tolerance head.positive) remaining).width_le
            |>.trans_lt (process.accurate state head.tolerance head.positive)
      | tail _ tailMember =>
          exact runRequests_width_lt_of_mem process
            (process.request state head.tolerance head.positive)
            remaining request tailMember

/-- Any two explicitly supplied values admitted at the final state are indistinguishable at every tolerance in the
finite batch. -/
theorem runRequests_pairwise_difference_lt_of_mem
    (process : Approximation.BoundProcess) (state : process.State)
    (requests : List Approximation.AccuracyRequest) (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) {left right : Fraction.Rational}
    (leftInside :
      (process.bound (process.runRequests state requests)).Contains left)
    (rightInside :
      (process.bound (process.runRequests state requests)).Contains right) :
    left - right < request.tolerance ∧
      right - left < request.tolerance := by
  have pairwise := Interval.pairwise_difference_le leftInside rightInside
  have accurate := process.runRequests_width_lt_of_mem
    state requests request member
  exact ⟨pairwise.1.trans_lt accurate, pairwise.2.trans_lt accurate⟩

/-- Canonical rational representative of the final state of a displayed finite request batch. -/
def runRequestsApproximation (process : Approximation.BoundProcess)
    (state : process.State) (requests : List Approximation.AccuracyRequest) : Fraction.Rational :=
  (process.bound (process.runRequests state requests)).sample

/-- The batch's computed rational representative lies in its final enclosure. -/
theorem runRequestsApproximation_inside (process : Approximation.BoundProcess)
    (state : process.State) (requests : List Approximation.AccuracyRequest) :
    (process.bound (process.runRequests state requests)).Contains
      (process.runRequestsApproximation state requests) :=
  (process.bound (process.runRequests state requests)).sample_contains

/-- The one rational representative computed after a finite batch is close to every rational admitted at that final
state, at every tolerance appearing in the batch. -/
theorem runRequests_candidate_close_to_approximation_of_mem
    (process : Approximation.BoundProcess) (state : process.State)
    (requests : List Approximation.AccuracyRequest) (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) {candidate : Fraction.Rational}
    (inside :
      (process.bound (process.runRequests state requests)).Contains candidate) :
    candidate - process.runRequestsApproximation state requests <
        request.tolerance ∧
      process.runRequestsApproximation state requests - candidate <
        request.tolerance :=
  process.runRequests_pairwise_difference_lt_of_mem state requests request
    member inside (process.runRequestsApproximation_inside state requests)

/-- A finite request batch also refines the process's distinguished initial bound, even when execution starts from an
arbitrary displayed state. -/
theorem runRequests_refines_initial (process : Approximation.BoundProcess)
    (state : process.State) (requests : List Approximation.AccuracyRequest) :
    Interval.Refines (process.bound (process.runRequests state requests))
      (process.bound process.initial) :=
  (process.runRequests_refines state requests).trans
    (process.refinesInitial state)

end BoundProcess

namespace ProgressiveObservation
end ProgressiveObservation

end Purelib.Approximation

end
