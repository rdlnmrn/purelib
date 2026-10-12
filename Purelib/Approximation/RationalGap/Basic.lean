module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic

import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.Bound.Schedule
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.Interval.Exclusion
import Init.Prelude
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

@[expose] public section

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

namespace Purelib.Approximation

namespace Bound
end Bound

set_option genInjectivity false in
/-- A finite rational enclosure process with an executable operation that separates its putative value from each
individually supplied rational. -/
structure RationalGapProcess where
  /-- The original rational enclosure process whose states and bounds are retained. -/ process :
    Approximation.BoundProcess
  /-- Refine a supplied process state to exclude one explicitly presented rational candidate. -/ separate :
    process.State → Fraction.Rational → process.State
  /-- The candidate-separation step refines its original enclosure. -/ separate_refines : ∀ state candidate,
    Interval.Refines (process.bound (separate state candidate))
      (process.bound state)
  /-- The separated enclosure excludes the exact supplied candidate. -/ separate_excludes : ∀ state candidate,
    (process.bound (separate state candidate)).Excludes candidate

constructive_injectivity RationalGapProcess

namespace RationalGapProcess

/-- Sequentially exclude a displayed finite list of rational candidates. -/
def runExclusions (gap : Purelib.Approximation.RationalGapProcess) :
    gap.process.State → List Purelib.Data.Rat.Fraction.Rational → gap.process.State
  | state, [] => state
  | state, candidate :: remaining =>
      runExclusions gap (gap.separate state candidate) remaining

/-- An empty exclusion list leaves the supplied state unchanged. -/
@[simp] theorem runExclusions_nil (gap :
  Approximation.RationalGapProcess)
    (state : gap.process.State) : gap.runExclusions state [] = state := rfl

/-- Exclude the first rational candidate before processing the remaining list. -/
@[simp] theorem runExclusions_cons (gap :
  Approximation.RationalGapProcess)
    (state : gap.process.State) (candidate : Fraction.Rational)
    (remaining : List Fraction.Rational) :
    gap.runExclusions state (candidate :: remaining) =
      gap.runExclusions (gap.separate state candidate) remaining := rfl

/-- A finite exclusion run refines its starting enclosure. -/
theorem runExclusions_refines (gap : Approximation.RationalGapProcess) :
    ∀ (state : gap.process.State) (candidates : List Fraction.Rational),
      Interval.Refines
        (gap.process.bound (gap.runExclusions state candidates))
        (gap.process.bound state)
  | _, [] => Refines.refl _
  | state, candidate :: remaining =>
      (runExclusions_refines gap (gap.separate state candidate)
        remaining).trans
        (gap.separate_refines state candidate)

/-- The final state excludes every rational in the displayed finite list. -/
theorem runExclusions_excludes_of_mem (gap :
  Approximation.RationalGapProcess) :
    ∀ (state : gap.process.State) (candidates : List Fraction.Rational)
      (candidate : Fraction.Rational),
      candidate ∈ candidates →
      (gap.process.bound
        (gap.runExclusions state candidates)).Excludes candidate
  | _, [], _, member => by
      cases member
  | state, head :: remaining, candidate, member => by
      cases member with
      | head =>
          exact (Approximation.RationalGapProcess.runExclusions_refines gap
            (gap.separate state head) remaining).excludes
              (gap.separate_excludes state head)
      | tail _ tailMember =>
          exact runExclusions_excludes_of_mem gap
            (gap.separate state head) remaining candidate tailMember

/-- First exclude a displayed finite rational list, then execute a displayed finite accuracy batch. -/
def inspect (gap : Approximation.RationalGapProcess) (state :
  gap.process.State)
    (candidates : List Fraction.Rational) (requests : List Approximation.AccuracyRequest) :
    gap.process.State :=
  gap.process.runRequests (gap.runExclusions state candidates) requests

/-- A finite inspection retains every requested rational exclusion. -/
theorem inspect_excludes_of_mem (gap : Approximation.RationalGapProcess)
    (state : gap.process.State) (candidates : List Fraction.Rational)
    (requests : List Approximation.AccuracyRequest) (candidate : Fraction.Rational)
    (member : candidate ∈ candidates) :
    (gap.process.bound
      (gap.inspect state candidates requests)).Excludes candidate := by
  exact (gap.process.runRequests_refines
    (gap.runExclusions state candidates) requests).excludes
      (gap.runExclusions_excludes_of_mem state candidates candidate member)

/-- The same finite inspection meets every displayed accuracy demand. -/
theorem inspect_width_lt_of_mem (gap : Approximation.RationalGapProcess)
    (state : gap.process.State) (candidates : List Fraction.Rational)
    (requests : List Approximation.AccuracyRequest) (request : Approximation.AccuracyRequest)
    (member : request ∈ requests) :
    (gap.process.bound (gap.inspect state candidates requests)).width <
      request.tolerance :=
  gap.process.runRequests_width_lt_of_mem
    (gap.runExclusions state candidates) requests request member

/-- A finite inspection remains a refinement of the supplied starting state. -/
theorem inspect_refines (gap : Approximation.RationalGapProcess)
    (state : gap.process.State) (candidates : List Fraction.Rational)
    (requests : List Approximation.AccuracyRequest) :
    Interval.Refines (gap.process.bound (gap.inspect state candidates requests))
      (gap.process.bound state) :=
  (gap.process.runRequests_refines
    (gap.runExclusions state candidates) requests).trans
      (gap.runExclusions_refines state candidates)

end RationalGapProcess

end Purelib.Approximation

end
