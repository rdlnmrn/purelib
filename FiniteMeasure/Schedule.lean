import FiniteMeasure.Protocol

/-!
# Finite batches of arbitrary-accuracy requests

This module isolates a useful replacement for an appeal to an infinite
limit: every displayed finite list of positive rational demands has one
explicit final state satisfying all of them.  Preservation comes from finite
refinement, not compactness or a completed intersection.
-/

namespace FiniteMeasure

/-- One positive rational accuracy demand. -/
structure AccuracyRequest where
  tolerance : Coordinate
  positive : 0 < tolerance

namespace BoundProcess

/-- Execute a displayed finite list of requests. -/
def runRequests (process : BoundProcess) :
    process.State → List AccuracyRequest → process.State
  | state, [] => state
  | state, request :: remaining =>
      runRequests process
        (process.request state request.tolerance request.positive) remaining

@[simp] theorem runRequests_nil (process : BoundProcess)
    (state : process.State) : process.runRequests state [] = state := rfl

@[simp] theorem runRequests_cons (process : BoundProcess)
    (state : process.State) (request : AccuracyRequest)
    (remaining : List AccuracyRequest) :
    process.runRequests state (request :: remaining) =
      process.runRequests
        (process.request state request.tolerance request.positive) remaining :=
  rfl

/-- The result of any finite request batch refines its starting state. -/
theorem runRequests_refines (process : BoundProcess) :
    ∀ (state : process.State) (requests : List AccuracyRequest),
      Bound.Refines (process.bound (process.runRequests state requests))
        (process.bound state)
  | _, [] => Bound.Refines.refl _
  | state, request :: remaining =>
      (runRequests_refines process
        (process.request state request.tolerance request.positive) remaining).trans
      (process.request_refines state request.tolerance request.positive)

/-- The last state of a finite batch satisfies every demand appearing in the
batch, not merely its final demand. -/
theorem runRequests_width_lt_of_mem (process : BoundProcess) :
    ∀ (state : process.State) (requests : List AccuracyRequest)
      (request : AccuracyRequest),
      request ∈ requests →
      (process.bound (process.runRequests state requests)).width <
        request.tolerance
  | state, [], request, member => by
      simp only [List.not_mem_nil] at member
  | state, head :: remaining, request, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst request
        exact (runRequests_refines process
          (process.request state head.tolerance head.positive) remaining).width_le
          |>.trans_lt (process.accurate state head.tolerance head.positive)
      · exact runRequests_width_lt_of_mem process
          (process.request state head.tolerance head.positive)
          remaining request tailMember

/-- Any two explicitly supplied values admitted at the final state are
indistinguishable at every tolerance in the finite batch. -/
theorem runRequests_pairwise_difference_lt_of_mem
    (process : BoundProcess) (state : process.State)
    (requests : List AccuracyRequest) (request : AccuracyRequest)
    (member : request ∈ requests) {left right : Coordinate}
    (leftInside :
      (process.bound (process.runRequests state requests)).Contains left)
    (rightInside :
      (process.bound (process.runRequests state requests)).Contains right) :
    left - right < request.tolerance ∧
      right - left < request.tolerance := by
  have pairwise := Bound.pairwise_difference_le leftInside rightInside
  have accurate := process.runRequests_width_lt_of_mem
    state requests request member
  exact ⟨pairwise.1.trans_lt accurate, pairwise.2.trans_lt accurate⟩

/-- Canonical rational representative of the final state of a displayed
finite request batch. -/
def runRequestsApproximation (process : BoundProcess)
    (state : process.State) (requests : List AccuracyRequest) : Coordinate :=
  (process.bound (process.runRequests state requests)).sample

theorem runRequestsApproximation_inside (process : BoundProcess)
    (state : process.State) (requests : List AccuracyRequest) :
    (process.bound (process.runRequests state requests)).Contains
      (process.runRequestsApproximation state requests) :=
  (process.bound (process.runRequests state requests)).sample_contains

/-- The one rational representative computed after a finite batch is close
to every rational admitted at that final state, at every tolerance appearing
in the batch. -/
theorem runRequests_candidate_close_to_approximation_of_mem
    (process : BoundProcess) (state : process.State)
    (requests : List AccuracyRequest) (request : AccuracyRequest)
    (member : request ∈ requests) {candidate : Coordinate}
    (inside :
      (process.bound (process.runRequests state requests)).Contains candidate) :
    candidate - process.runRequestsApproximation state requests <
        request.tolerance ∧
      process.runRequestsApproximation state requests - candidate <
        request.tolerance :=
  process.runRequests_pairwise_difference_lt_of_mem state requests request
    member inside (process.runRequestsApproximation_inside state requests)

/-- A finite request batch also refines the process's distinguished initial
bound, even when execution starts from an arbitrary displayed state. -/
theorem runRequests_refines_initial (process : BoundProcess)
    (state : process.State) (requests : List AccuracyRequest) :
    Bound.Refines (process.bound (process.runRequests state requests))
      (process.bound process.initial) :=
  (process.runRequests_refines state requests).trans
    (process.refinesInitial state)

end BoundProcess

namespace ProgressiveObservation

/-- Execute a displayed finite list of observation requests. -/
def runRequests
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance) :
    name.State → List AccuracyRequest → name.State
  | state, [] => state
  | state, request :: remaining =>
      runRequests name
        (name.request state request.tolerance request.positive) remaining

@[simp] theorem runRequests_nil
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance) (state : name.State) :
    name.runRequests state [] = state := rfl

@[simp] theorem runRequests_cons
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance) (state : name.State)
    (request : AccuracyRequest) (remaining : List AccuracyRequest) :
    name.runRequests state (request :: remaining) =
      name.runRequests
        (name.request state request.tolerance request.positive) remaining :=
  rfl

/-- The final observation predicate refines the starting predicate. -/
theorem runRequests_refines
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance) :
    ∀ (state : name.State) (requests : List AccuracyRequest),
      Observation.Refines
        (name.observation (name.runRequests state requests))
        (name.observation state)
  | _, [] => Observation.Refines.refl _
  | state, request :: remaining =>
      (runRequests_refines name
        (name.request state request.tolerance request.positive) remaining).trans
      (name.request_refines state request.tolerance request.positive)

/-- Every two candidates admitted after a finite batch meet every tolerance
in that batch.  The final observation's stored spread need not be compared
numerically with earlier spreads; predicate refinement is sufficient. -/
theorem runRequests_pairwise_lt_of_mem
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance) :
    ∀ (state : name.State) (requests : List AccuracyRequest)
      (request : AccuracyRequest),
      request ∈ requests →
      ∀ {left right : α},
        (name.observation (name.runRequests state requests)).Possible left →
        (name.observation (name.runRequests state requests)).Possible right →
        distance left right < request.tolerance
  | _, [], _, member, _, _, _, _ => by
      simp only [List.not_mem_nil] at member
  | state, head :: remaining, request, member,
      left, right, leftPossible, rightPossible => by
      simp only [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst request
        have refines := runRequests_refines name
          (name.request state head.tolerance head.positive) remaining
        have leftEarlier := refines.possible leftPossible
        have rightEarlier := refines.possible rightPossible
        exact (name.observation
            (name.request state head.tolerance head.positive)).pairwise
              leftEarlier rightEarlier |>.trans_lt
          (name.accurate state head.tolerance head.positive)
      · exact runRequests_pairwise_lt_of_mem name
          (name.request state head.tolerance head.positive)
          remaining request tailMember leftPossible rightPossible

/-- The explicit final witness after a finite batch still satisfies the
distinguished initial predicate. -/
theorem runRequests_witness_possible_initial
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance)
    (state : name.State) (requests : List AccuracyRequest) :
    (name.observation name.initial).Possible
      (name.observation (name.runRequests state requests)).witness :=
  (name.runRequests_refines state requests).trans
    (name.refinesInitial state) |>.witness_possible

end ProgressiveObservation

end FiniteMeasure
