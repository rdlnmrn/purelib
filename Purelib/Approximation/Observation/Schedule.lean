module
import Purelib.Data.Rat.Fraction

public import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Observation.Basic
public import Purelib.Approximation.Observation.Process
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Observation

open Purelib.Data.Rat

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
end BoundProcess

namespace ProgressiveObservation

/-- Execute a displayed finite list of observation requests. -/
def runRequests
    {α : Type} {distance : α → α → Purelib.Data.Rat.Fraction.Rational}
    (name : Purelib.Approximation.ProgressiveObservation α distance) :
    name.State → List Purelib.Approximation.AccuracyRequest → name.State
  | state, [] => state
  | state, request :: remaining =>
      runRequests name
        (name.request state request.tolerance request.positive) remaining

/-- An empty observation-request batch returns the supplied state. -/
@[simp] theorem runRequests_nil
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance) (state : name.State) :
    name.runRequests state [] = state := rfl

/-- A nonempty observation batch executes its first request before the remaining requests. -/
@[simp] theorem runRequests_cons
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance) (state : name.State)
    (request : Approximation.AccuracyRequest) (remaining : List Approximation.AccuracyRequest) :
    name.runRequests state (request :: remaining) =
      name.runRequests
        (name.request state request.tolerance request.positive) remaining :=
  rfl

/-- The final observation predicate refines the starting predicate. -/
theorem runRequests_refines
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance) :
    ∀ (state : name.State) (requests : List Approximation.AccuracyRequest),
      Observation.Refines
        (name.observation (name.runRequests state requests))
        (name.observation state)
  | _, [] => Refines.refl _
  | state, request :: remaining =>
      (runRequests_refines name
        (name.request state request.tolerance request.positive) remaining).trans
      (name.request_refines state request.tolerance request.positive)

/-- Every two candidates admitted after a finite batch meet every tolerance in that batch. The final observation's
stored spread need not be compared numerically with earlier spreads; predicate refinement is sufficient. -/
theorem runRequests_pairwise_lt_of_mem
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance) :
    ∀ (state : name.State) (requests : List Approximation.AccuracyRequest)
      (request : Approximation.AccuracyRequest),
      request ∈ requests →
      ∀ {left right : α},
        (name.observation (name.runRequests state requests)).Possible left →
        (name.observation (name.runRequests state requests)).Possible right →
        distance left right < request.tolerance
  | _, [], _, member, _, _, _, _ => by
      cases member
  | state, head :: remaining, request, member,
      left, right, leftPossible, rightPossible => by
      cases member with
      | head =>
          have refines := runRequests_refines name
            (name.request state head.tolerance head.positive) remaining
          have leftEarlier := refines.possible leftPossible
          have rightEarlier := refines.possible rightPossible
          exact (name.observation
              (name.request state head.tolerance head.positive)).pairwise
                leftEarlier rightEarlier |>.trans_lt
            (name.accurate state head.tolerance head.positive)
      | tail _ tailMember =>
          exact runRequests_pairwise_lt_of_mem name
            (name.request state head.tolerance head.positive)
            remaining request tailMember leftPossible rightPossible

/-- The explicit final witness after a finite batch still satisfies the distinguished initial predicate. -/
theorem runRequests_witness_possible_initial
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance)
    (state : name.State) (requests : List Approximation.AccuracyRequest) :
    (name.observation name.initial).Possible
      (name.observation (name.runRequests state requests)).witness :=
  (name.runRequests_refines state requests).trans
    (name.refinesInitial state) |>.witness_possible

end ProgressiveObservation

end Purelib.Approximation

end
