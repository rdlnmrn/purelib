module

public import Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.RootContinuation.CoherentRoot
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Checked finite common-root refinement attempts

The second original owner is refined once at the specified positive index.
Its strict inclusion into that same original owner is automatic. The actual
four-side strict-containment test into the first original owner either
constructs the existing CommonRefinement or retains the exact attempted
owner and the unresolved first-owner containment. A stopped attempt states
no global root mismatch or impossibility of a later common refinement.
-/

public section

namespace Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (state_strict_initial_of_pos)

set_option genInjectivity false in
/-- The actual result of one positive-index common-refinement containment check.

Success retains the existing complete CommonRefinement and the exact paid
index. Incompleteness retains the original second-owner refinement, its full
factory equation, the internally paid second-owner inclusion and the actual
failed first-owner strict-containment obligation.
-/
inductive Outcome {parameter : Canonical} (first second : Owner parameter) (stage : Nat) : Type 1 where
  /-- The actual retained common owner satisfies both strict inclusions at this attempted index. -/
  | ready (common : CommonRefinement first second) (index_eq : common.index = stage + 1)
  /-- This finite attempt stopped at an actual original refinement without paying the first strict inclusion. -/
  | inconclusive (candidate : Owner parameter) (candidate_eq : candidate = second.refineAt (stage + 1))
      (strictSecond : candidate.track.initial.box.StrictInterior second.track.initial.box)
      (unpaid : ¬ candidate.track.initial.box.StrictInterior first.track.initial.box)

constructive_injectivity Outcome

namespace Outcome

variable {parameter : Canonical} {first second : Owner parameter} {stage : Nat}

/-- The actual specified refinement passed both original-owner strict-containment checks. -/
@[expose] def Ready : Outcome first second stage → Prop
  | .ready _ _ => True
  | .inconclusive _ _ _ _ => False

/-- Read the identical actual candidate retained by either outcome without another owner refinement. -/
@[expose] def candidate (outcome : Outcome first second stage) : Owner parameter :=
  match outcome with
  | .ready common _ => common.owner
  | .inconclusive retained _ _ _ => retained

/-- Both outcomes preserve the entire specified refinement of the same original second owner. -/
theorem candidate_eq (outcome : Outcome first second stage) :
    outcome.candidate = second.refineAt (stage + 1) := by
  cases outcome with
  | ready common index_eq => exact common.owner_eq.trans (congrArg second.refineAt index_eq)
  | inconclusive candidate candidate_eq _ _ => exact candidate_eq

/-- The candidate's strict inclusion in its original second owner is paid in both outcomes. -/
theorem strictSecond (outcome : Outcome first second stage) :
    outcome.candidate.track.initial.box.StrictInterior second.track.initial.box := by
  cases outcome with
  | ready common _ => exact common.strictSecond
  | inconclusive _ _ paid _ => exact paid

end Outcome

/-- Check one actual positive-index second-owner refinement for strict inclusion in both original owners.

Only the second original owner's retained refinement operation is executed.
The existing decidable four-coordinate box test determines whether that
same actual candidate is a common refinement. The requested stage is a
finite stopping request; no operational equivalence is presumed.
-/
def checkAt {parameter : Canonical} (first second : Owner parameter) (stage : Nat) :
    Outcome first second stage :=
  let candidate := second.refineAt (stage + 1)
  have strictSecond : candidate.track.initial.box.StrictInterior second.track.initial.box :=
    state_strict_initial_of_pos second.track (Nat.zero_lt_succ stage)
  if paid : candidate.track.initial.box.StrictInterior first.track.initial.box then
    .ready ⟨stage + 1, candidate, rfl, paid, strictSecond⟩ rfl
  else
    .inconclusive candidate rfl strictSecond paid

namespace CommonRefinement

variable {parameter : Canonical} {first second : Owner parameter}

/-- Every later original second-owner state retains the common refinement's strict first-owner inclusion.

The original common-owner factory identifies its exact second-track state.
Nesting that same track preserves the already paid four strict margins; no
new root comparison, owner refinement or candidate selection is executed.
-/
theorem strictFirst_at (common : CommonRefinement first second) (index : Nat) (later : common.index ≤ index) :
    (second.refineAt index).track.initial.box.StrictInterior first.track.initial.box := by
  have strict := common.strictFirst
  rewrite [common.owner_eq] at strict
  exact Geometry.Rational.Box.Refinement.StrictInterior.of_refines strict
    (CoherentRoot.state_refines_of_le second.track later)

end CommonRefinement

/-- The same finite check succeeds when its actual candidate's first-owner strict inclusion is paid. -/
theorem checkAt_ready_of_strict {parameter : Canonical} (first second : Owner parameter) (stage : Nat)
    (paid : (second.refineAt (stage + 1)).track.initial.box.StrictInterior first.track.initial.box) :
    Outcome.Ready (checkAt first second stage) := by
  unfold checkAt
  rewrite [dif_pos paid]
  exact True.intro

/-- A retained common refinement gives a sufficient finite index for the identical original containment check.

The request may exceed the original selected index. This is a quantitative
success theorem for the stated original check, not a claim that executing
that check reuses the previously computed common owner's refinement work.
-/
theorem checkAt_ready_of_common {parameter : Canonical} {first second : Owner parameter}
    (common : CommonRefinement first second) (stage : Nat) (later : common.index ≤ stage + 1) :
    Outcome.Ready (checkAt first second stage) :=
  checkAt_ready_of_strict first second stage (common.strictFirst_at (stage + 1) later)

end Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement

end
