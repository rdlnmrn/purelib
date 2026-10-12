module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Process.Sampling
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

section
@[expose] public section

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement

set_option genInjectivity false in
/-- Retained automatic-search state for one fixed coherent denominator. `persists` records finite provenance back to the
denominator's original named state, while `nextIndex` selects the next canonical positive rational request. -/
structure State (denominator :
  Coherent.CoherentNamed) where
  /-- The retained state of the original denominator process. -/ source : denominator.name.process.State
  /-- The index of the next canonical positive rational refinement request. -/ nextIndex : Nat
  /-- Every candidate possible at the retained state remains possible at the original denominator state. -/ persists : ∀
    {value : Canonical},
    denominator.name.process.Possible source value →
      denominator.name.process.Possible denominator.name.state value

constructive_injectivity State

namespace State.mk

end State.mk

namespace State

/-- The initial search state performs no refinement and has reflexive candidate provenance. -/
def initial (denominator :
  Coherent.CoherentNamed) : State denominator where
  source := denominator.name.state
  nextIndex := 0
  persists := fun possible => possible

/-- One deterministic unit of automatic work. The retained source is refined in place, and its provenance proof is
composed with refinement persistence. -/
def advance {denominator :
  Coherent.CoherentNamed}
    (state : State denominator) :
      State denominator where
  source := denominator.name.process.refine state.source
    (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex)
  nextIndex := state.nextIndex + 1
  persists := fun possible =>
    state.persists
      (denominator.name.process.refine_persists state.source
        (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
        (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex)
        possible)

/-- The initial search retains the denominator's original named state. -/
@[simp] theorem initial_source (denominator :
  Coherent.CoherentNamed) :
    (initial denominator).source = denominator.name.state :=
      rfl

/-- The initial search begins at refinement index zero. -/
@[simp] theorem initial_nextIndex
  (denominator : Coherent.CoherentNamed) :
    (initial denominator).nextIndex = 0 := rfl

/-- Advancing the search performs the canonical refinement of its retained source state. -/
@[simp] theorem advance_source {denominator :
  Coherent.CoherentNamed}
    (state : State denominator) :
    state.advance.source = denominator.name.process.refine state.source
      (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
      (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex) := rfl

/-- Advancing the search increments the refinement index by one. -/
@[simp] theorem advance_nextIndex
  {denominator : Coherent.CoherentNamed}
    (state : State denominator) :
    state.advance.nextIndex = state.nextIndex + 1 := rfl

/-- Every retained candidate still has the promised provenance at the original named denominator state. -/
theorem possible_at_initial {denominator :
  Coherent.CoherentNamed}
    (state : State denominator) {value :
      Canonical}
    (possible : denominator.name.process.Possible state.source value) :
    denominator.name.process.Possible denominator.name.state value :=
  state.persists possible

end State

namespace State

/-- A genuine automatic transition. There is exactly one transition from a state: its canonical finite refinement. -/
inductive Progress {denominator :
  Coherent.CoherentNamed} :
    State denominator →
      State denominator → Type
  /-- The canonical single refinement transition from a retained search state. -/ | refined (state :
    State denominator) :
    Progress state state.advance

end State

namespace State.Progress

/-- One automatic transition preserves every candidate admitted by its target as a candidate admitted by its source. -/
theorem possible_persists {denominator :
  Coherent.CoherentNamed}
    {current next : State denominator} (progress :
      Approximation.Gaussian.Name.Coherent.Refinement.State.Progress current next)
    {value : Canonical}
    (possible : denominator.name.process.Possible next.source value) :
    denominator.name.process.Possible current.source value := by
  cases progress
  exact denominator.name.process.refine_persists current.source
    (Gaussian.Process.Sampling.refinementTarget current.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos current.nextIndex)
    possible

/-- Every certified automatic transition increments the refinement index by one. -/
@[simp] theorem nextIndex_eq {denominator
  : Coherent.CoherentNamed}
    {current next : State denominator} (progress :
      Approximation.Gaussian.Name.Coherent.Refinement.State.Progress current next) :
    next.nextIndex = current.nextIndex + 1 := by
  cases progress
  rfl

end State.Progress

namespace State

set_option genInjectivity false in
/-- Finite reflexive-transitive reachability generated only by certified automatic refinement steps. No completed
execution history is stored. -/
inductive Reachable {denominator :
  Coherent.CoherentNamed} :
    State denominator →
      State denominator → Type
  /-- The empty finite refinement path from a state to itself. -/ | refl (state :
    State denominator) :
    Reachable state state
  /-- Prepend one certified refinement transition to an existing finite path. -/ | tail {first middle last :
    State denominator} :
      Approximation.Gaussian.Name.Coherent.Refinement.State.Progress first middle →
        Reachable middle last →
        Reachable first last

constructive_injectivity Reachable

end State

namespace State.Reachable.tail

end State.Reachable.tail

namespace State.Reachable

/-- Candidate persistence composes along every finite execution. -/
theorem possible_persists {denominator :
  Coherent.CoherentNamed}
    {first last : State denominator} (reachable :
      Approximation.Gaussian.Name.Coherent.Refinement.State.Reachable first last)
    {value : Canonical}
    (possible : denominator.name.process.Possible last.source value) :
    denominator.name.process.Possible first.source value := by
  induction reachable with
  | refl => exact possible
  | tail progress reachable inductionHypothesis =>
      exact progress.possible_persists (inductionHypothesis possible)

end State.Reachable
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement

end

section
@[expose] public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

section Purelib.CCL.Progressive.PartialLogQuotient

section Division
end Division
end Purelib.CCL.Progressive.PartialLogQuotient

end
