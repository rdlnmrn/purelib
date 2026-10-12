module

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Process.Sampling
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# Retryable finite preflight for one anchored logarithm branch

The source anchor fixes the logarithm branch.  Automatic work refines one
target coherent name until an executable rational chart-safety certificate is
visible.  Generic finite refinement cannot construct semantic overlap between
two unrelated `Possible` predicates, so success of the safety test returns a
typed `blocked` requirement for an overlap witness at the exact prepared target
state.  Supplying that witness resumes directly into the existing
`SafeOverlapExtension.transport` operation.

No output name is exposed before readiness.  Failure of a safety test performs
one certified refinement and never proves that the input is zero or outside a
logarithm domain.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState

set_option genInjectivity false in
/-- Retained automatic-search state for one fixed target name. -/
structure State (target : Coherent.CoherentNamed) where
  /-- The exact retained state of the original target process. -/ source : target.name.process.State
  /-- The index of the next canonical refinement request. -/ nextIndex : Nat
  /-- Every candidate at the retained source remains possible at the original target state. -/ persists : ∀ {value :
    Canonical},
    target.name.process.Possible source value →
      target.name.process.Possible target.name.state value

constructive_injectivity State

namespace State

/-- Start logarithm refinement at the original target process state with schedule index zero. -/
def initial (target : Coherent.CoherentNamed) : Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State
  target where
  source := target.name.state
  nextIndex := 0
  persists := fun possible => possible

/-- Refine the retained target state at its next scheduled precision and increment the schedule index.

The resulting persistence certificate still refers to the original target state. -/
def advance {target : Coherent.CoherentNamed} (state :
  Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State target) :
  Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State target where
  source := target.name.process.refine state.source
    (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex)
  nextIndex := state.nextIndex + 1
  persists := fun possible =>
    state.persists
      (target.name.process.refine_persists state.source
        (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
        (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex)
        possible)

/-- Initial logarithm refinement retains the original target process state. -/
@[simp] theorem initial_source
  (target : Coherent.CoherentNamed) :
    (Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State.initial target).source = target.name.state :=
      rfl

/-- Initial logarithm refinement starts at schedule index zero. -/
@[simp] theorem initial_nextIndex
  (target : Coherent.CoherentNamed) :
    (Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State.initial target).nextIndex = 0 := rfl

/-- Advancing uses the scheduled refinement of the exact retained source state. -/
@[simp] theorem advance_source
  {target : Coherent.CoherentNamed} (state : Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State
  target) :
    state.advance.source = target.name.process.refine state.source
      (Gaussian.Process.Sampling.refinementTarget state.nextIndex)
      (Gaussian.Process.Sampling.refinementTarget_pos state.nextIndex) := rfl

/-- Advancing logarithm refinement increments the schedule index by one. -/
@[simp] theorem advance_nextIndex
  {target : Coherent.CoherentNamed}
    (state : Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State target) :
    state.advance.nextIndex = state.nextIndex + 1 := rfl

end State

/-- One certified automatic refinement step. -/
inductive Progress {target : Coherent.CoherentNamed} :
  State target →
  State target → Prop
  /-- Certify the canonical single refinement from a state to its advance. -/ | refined (state :
    State target) :
    Progress state state.advance

namespace Progress

/-- A certified refinement step preserves possible readings backwards to its original source. -/
theorem possible_persists {target : Coherent.CoherentNamed}
    {current next : Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State target} (progress :
      Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.Progress current next)
    {value : Canonical}
    (possible : target.name.process.Possible next.source value) :
    target.name.process.Possible current.source value := by
  cases progress
  exact target.name.process.refine_persists current.source
    (Gaussian.Process.Sampling.refinementTarget current.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos current.nextIndex)
    possible

/-- One certified refinement step increases the schedule index by exactly one. -/
@[simp] theorem nextIndex_eq
  {target : Coherent.CoherentNamed}
    {current next : Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State target} (progress :
      Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.Progress current next) :
    next.nextIndex = current.nextIndex + 1 := by
  cases progress
  rfl

end Progress

/-- Finite reachability generated only by genuine refinement progress. -/
inductive Reachable {target : Coherent.CoherentNamed} :
  State target →
  State target → Prop
  /-- Certify reachability without taking a refinement step. -/ | refl (state :
    State target) :
    Reachable state state
  /-- Prepend one certified refinement step to a finite reachability certificate. -/ | tail {start middle finish :
    State target} :
      Progress start middle →
        Reachable middle finish →
        Reachable start finish

namespace Reachable

/-- Finite certified refinement reachability preserves possible readings backwards to its starting source. -/
theorem possible_persists {target : Coherent.CoherentNamed}
    {start finish : Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State target} (reachable :
      Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.Reachable start finish)
    {value : Canonical}
    (possible : target.name.process.Possible finish.source value) :
    target.name.process.Possible start.source value := by
  induction reachable with
  | refl state => exact possible
  | tail progress later inductionHypothesis =>
      exact progress.possible_persists (inductionHypothesis possible)

end Reachable

/-- The coherent target restricted to the successful finite refinement future. -/
def preparedTarget {target : Coherent.CoherentNamed} (state :
  State target) :
    Coherent.CoherentNamed :=
  CoherentNamed.based target state.source

/-- Every prepared target retains the operational value of the original target name. -/
def preparedTargetEquivalent {target : Coherent.CoherentNamed} (state :
  State target) :
    Gaussian.Equivalence.NamedEquivalent target.name
      (preparedTarget state).name :=
  CoherentNamed.basedEquivalent target state.source

/-- Prepared targets reached on two different finite schedules remain operationally equivalent. -/
def preparedTargetsEquivalent {target : Coherent.CoherentNamed}
    (first second : State target) :
    Gaussian.Equivalence.NamedEquivalent (preparedTarget
      first).name (preparedTarget second).name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm
      (preparedTargetEquivalent first))
    (preparedTargetEquivalent second)
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState

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

end

end
