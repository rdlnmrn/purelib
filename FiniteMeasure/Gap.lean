import FiniteMeasure.Schedule

/-!
# Finitely testable rational gaps

`RationalGapProcess` is an interface for a bound process that can exclude any
rational candidate when that candidate is actually presented.  A finite
inspection can exclude every member of a displayed rational list and meet
every member of a displayed accuracy list at once.

This does not construct an irrational point, enumerate the rationals, or
assert one state excluding all rationals.  It records exactly the operational
content available to finite tests.
-/

namespace FiniteMeasure

namespace Bound

/-- A rational enclosure explicitly lies wholly to one side of a displayed
rational candidate. -/
def Excludes (bound : Bound) (candidate : Coordinate) : Prop :=
  candidate < bound.lower ∨ bound.upper < candidate

instance excludesDecidable (bound : Bound) (candidate : Coordinate) :
    Decidable (bound.Excludes candidate) := by
  unfold Excludes
  infer_instance

/-- Narrowing an enclosure preserves every rational exclusion already
obtained. -/
theorem Refines.excludes {inner outer : Bound}
    (refines : Refines inner outer) {candidate : Coordinate}
    (excludes : outer.Excludes candidate) : inner.Excludes candidate := by
  rcases excludes with below | above
  · exact Or.inl (below.trans_le refines.lower)
  · exact Or.inr (refines.upper.trans_lt above)

end Bound

/-- A finite rational enclosure process with an executable operation that
separates its putative value from each individually supplied rational. -/
structure RationalGapProcess where
  process : BoundProcess
  separate : process.State → Coordinate → process.State
  separate_refines : ∀ state candidate,
    Bound.Refines (process.bound (separate state candidate))
      (process.bound state)
  separate_excludes : ∀ state candidate,
    (process.bound (separate state candidate)).Excludes candidate

namespace RationalGapProcess

/-- Sequentially exclude a displayed finite list of rational candidates. -/
def runExclusions (gap : RationalGapProcess) :
    gap.process.State → List Coordinate → gap.process.State
  | state, [] => state
  | state, candidate :: remaining =>
      runExclusions gap (gap.separate state candidate) remaining

@[simp] theorem runExclusions_nil (gap : RationalGapProcess)
    (state : gap.process.State) : gap.runExclusions state [] = state := rfl

@[simp] theorem runExclusions_cons (gap : RationalGapProcess)
    (state : gap.process.State) (candidate : Coordinate)
    (remaining : List Coordinate) :
    gap.runExclusions state (candidate :: remaining) =
      gap.runExclusions (gap.separate state candidate) remaining := rfl

/-- A finite exclusion run refines its starting enclosure. -/
theorem runExclusions_refines (gap : RationalGapProcess) :
    ∀ (state : gap.process.State) (candidates : List Coordinate),
      Bound.Refines
        (gap.process.bound (gap.runExclusions state candidates))
        (gap.process.bound state)
  | _, [] => Bound.Refines.refl _
  | state, candidate :: remaining =>
      (runExclusions_refines gap (gap.separate state candidate) remaining).trans
        (gap.separate_refines state candidate)

/-- The final state excludes every rational in the displayed finite list. -/
theorem runExclusions_excludes_of_mem (gap : RationalGapProcess) :
    ∀ (state : gap.process.State) (candidates : List Coordinate)
      (candidate : Coordinate),
      candidate ∈ candidates →
      (gap.process.bound
        (gap.runExclusions state candidates)).Excludes candidate
  | _, [], _, member => by
      simp only [List.not_mem_nil] at member
  | state, head :: remaining, candidate, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst candidate
        exact (runExclusions_refines gap
          (gap.separate state head) remaining).excludes
            (gap.separate_excludes state head)
      · exact runExclusions_excludes_of_mem gap
          (gap.separate state head) remaining candidate tailMember

/-- First exclude a displayed finite rational list, then execute a displayed
finite accuracy batch. -/
def inspect (gap : RationalGapProcess) (state : gap.process.State)
    (candidates : List Coordinate) (requests : List AccuracyRequest) :
    gap.process.State :=
  gap.process.runRequests (gap.runExclusions state candidates) requests

/-- A finite inspection retains every requested rational exclusion. -/
theorem inspect_excludes_of_mem (gap : RationalGapProcess)
    (state : gap.process.State) (candidates : List Coordinate)
    (requests : List AccuracyRequest) (candidate : Coordinate)
    (member : candidate ∈ candidates) :
    (gap.process.bound
      (gap.inspect state candidates requests)).Excludes candidate := by
  exact (gap.process.runRequests_refines
    (gap.runExclusions state candidates) requests).excludes
      (gap.runExclusions_excludes_of_mem state candidates candidate member)

/-- The same finite inspection meets every displayed accuracy demand. -/
theorem inspect_width_lt_of_mem (gap : RationalGapProcess)
    (state : gap.process.State) (candidates : List Coordinate)
    (requests : List AccuracyRequest) (request : AccuracyRequest)
    (member : request ∈ requests) :
    (gap.process.bound (gap.inspect state candidates requests)).width <
      request.tolerance :=
  gap.process.runRequests_width_lt_of_mem
    (gap.runExclusions state candidates) requests request member

/-- A finite inspection remains a refinement of the supplied starting
state. -/
theorem inspect_refines (gap : RationalGapProcess)
    (state : gap.process.State) (candidates : List Coordinate)
    (requests : List AccuracyRequest) :
    Bound.Refines (gap.process.bound (gap.inspect state candidates requests))
      (gap.process.bound state) :=
  (gap.process.runRequests_refines
    (gap.runExclusions state candidates) requests).trans
      (gap.runExclusions_refines state candidates)

end RationalGapProcess

end FiniteMeasure
