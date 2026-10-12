module

meta import Purelib.Elab.Deriving.Repr

import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint
public import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

section
@[expose] public section

/-!
# Certified finite translations between refinement protocols

This module separates two operations which cannot constructively be conflated.
A direct observation map converts only the information already present in one
finite observation.  A finite realizer may first refine its source in response
to a positive rational request and records the finite work performed.

Candidate readings are Gaussian rationals.  Relations between readings remain
explicit because an affine enclosure, a projective CCL tail, and a redundant
digit cell need not use identical internal coordinates.
-/

namespace Purelib.Approximation.Gaussian.Translation

set_option genInjectivity false in
/-- The observable finite actions performed by one translation request. -/
structure Schedule where
  /-- The number of source refinements performed. -/ sourceRefinements : Nat
  /-- The number of output units emitted. -/ emittedUnits : Nat
  /-- The number of recorded arithmetic steps. -/ arithmeticSteps : Nat
deriving DecidableEq

constructive_injectivity Schedule

derive_exposed_repr Schedule

namespace Schedule.mk

end Schedule.mk

namespace Schedule

/-- The deliberately simple reference cost model: every displayed action has unit cost. More specialized realizers may
expose sharper auxiliary bounds. -/
def work (schedule :
  Schedule) : Nat :=
  schedule.sourceRefinements + schedule.emittedUnits +
    schedule.arithmeticSteps

/-- The schedule with zero source refinements, emissions and arithmetic steps. -/
def zero :
  Schedule :=
  { sourceRefinements := 0
    emittedUnits := 0
    arithmeticSteps := 0 }

/-- Combine two finite schedules by adding their three action counts. -/
def add (left right :
  Schedule) : Schedule :=
  { sourceRefinements := left.sourceRefinements + right.sourceRefinements
    emittedUnits := left.emittedUnits + right.emittedUnits
    arithmeticSteps := left.arithmeticSteps + right.arithmeticSteps }

/-- The empty schedule has zero work. -/
@[simp] theorem work_zero :
  zero.work = 0 := rfl

/-- The work of a combined schedule is the sum of the two original work counts. -/
theorem work_add (left right :
  Schedule) :
    (left.add right).work = left.work + right.work := by
  change
    (left.sourceRefinements + right.sourceRefinements) +
          (left.emittedUnits + right.emittedUnits) +
        (left.arithmeticSteps + right.arithmeticSteps) =
      (left.sourceRefinements + left.emittedUnits + left.arithmeticSteps) +
        (right.sourceRefinements + right.emittedUnits + right.arithmeticSteps)
  omega

end Schedule

end Purelib.Approximation.Gaussian.Translation

end
