module

public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Observation.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Distance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Finite observations of retained Gaussian process states

The original possibility predicate and rational witness become a generic
finite observation. Its spread is the four-radius squared-distance bound.
Actual process refinement extends the existing observation history without
introducing another notion of refinement or selecting a completed value.
-/

public section

namespace Purelib.Approximation.Gaussian.Process

open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat

/-- Observe a retained process state with its original candidates and witness.

The displayed spread bounds the squared distance of any two candidates in
the state's actual ball. Neither the predicate nor its witness is replaced
by the larger set of all readings of that ball.
-/
@[expose] def observation (process : Gaussian.Process) (state : process.State) :
    Approximation.Observation Gaussian.Basic.Canonical
      (fun left right => Gaussian.Norm.Basic.normSq (left - right)) where
  Possible := process.Possible state
  witness := (process.witness state).val
  witness_possible := (process.witness state).property
  spread := 4 * (process.ball state).radiusSq
  spread_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide) (process.ball state).radiusSq_nonneg
  pairwise leftPossible rightPossible :=
    Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq
      (process.possible_inside leftPossible) (process.possible_inside rightPossible)

/-- An actual process refinement refines its generic finite observation. -/
theorem refine_observation (process : Gaussian.Process) (state : process.State)
    (target : Fraction.Rational) (positive : 0 < target) :
    Approximation.Observation.Refines
      (process.observation (process.refine state target positive))
      (process.observation state) :=
  ⟨fun possible => process.refine_persists state target positive possible⟩

set_option genInjectivity false in
/-- A retained observation caches the exact ball, possible witness and generic observation of one original state.

Both source readbacks are executed once. The generic observation consumes those
same retained values; its specification equality preserves the original state,
possibility predicate, witness and four-radius spread.
-/
structure Observation (process : Gaussian.Process) (state : process.State) where
  /-- The actual ball read once at the same original state. -/ ball : Enclosure.Ball
  /-- The retained ball is the original state's canonical numerical readback. -/ ballEq : ball = process.ball state
  /-- The actual original possible witness, including its possibility evidence. -/ witness :
    { value : Gaussian.Basic.Canonical // process.Possible state value }
  /-- The retained witness is the original state's actual witness. -/ witnessEq : witness = process.witness state
  /-- The same finite generic observation, prepared from the retained ball and witness. -/ generic :
    Approximation.Observation Gaussian.Basic.Canonical
      (fun left right => Gaussian.Norm.Basic.normSq (left - right))
  /-- The retained generic observation equals the original canonical specification. -/ genericEq :
    generic = process.observation state

namespace Observation

/-- Construct the generic observation from the exact already retained original ball and witness. -/
@[expose] def ofReadings (process : Gaussian.Process) (state : process.State)
    (ball : Enclosure.Ball) (ballEq : ball = process.ball state)
    (witness : { value : Gaussian.Basic.Canonical // process.Possible state value })
    (witnessEq : witness = process.witness state) : Observation process state := by
  let generic : Approximation.Observation Gaussian.Basic.Canonical
      (fun left right => Gaussian.Norm.Basic.normSq (left - right)) :=
    { Possible := process.Possible state
      witness := witness.val
      witness_possible := witness.property
      spread := 4 * ball.radiusSq
      spread_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) ball.radiusSq_nonneg
      pairwise := by
        intro left right leftPossible rightPossible
        rewrite [ballEq]
        exact Enclosure.Ball.Distance.normSq_sub_le_four_radiusSq
          (process.possible_inside leftPossible) (process.possible_inside rightPossible) }
  have genericEq : generic = process.observation state := by
    cases ballEq
    cases witnessEq
    rfl
  exact ⟨ball, ballEq, witness, witnessEq, generic, genericEq⟩

/-- Read the original state's ball and witness once and cache their shared finite generic observation. -/
@[expose] def build (process : Gaussian.Process) (state : process.State) : Observation process state :=
  let ball := process.ball state
  let witness := process.witness state
  ofReadings process state ball rfl witness rfl

/-- Two retained observations of the same original process state have the same complete cached data. -/
theorem unique {process : Gaussian.Process} {state : process.State}
    (first second : Observation process state) : first = second := by
  rcases first with ⟨firstBall, firstBallEq, firstWitness, firstWitnessEq, firstGeneric, firstGenericEq⟩
  rcases second with ⟨secondBall, secondBallEq, secondWitness, secondWitnessEq, secondGeneric, secondGenericEq⟩
  cases firstBallEq
  cases secondBallEq
  cases firstWitnessEq
  cases secondWitnessEq
  cases firstGenericEq
  cases secondGenericEq
  rfl

/-- Extend an existing generic history with the same retained older and newer observations.

The actual returned state and its defining refinement equality are supplied
from the original source transition. History constructors consume the retained
observation caches; no source refinement, ball or witness producer is called.
-/
@[expose] def extendHistory {process : Gaussian.Process} {initial before after : process.State}
    (older : Observation process before) (newer : Observation process after)
    (target : Fraction.Rational) (positive : 0 < target)
    (afterEq : after = process.refine before target positive)
    (history : Approximation.Observation.History (process.observation initial) (process.observation before)) :
    Approximation.Observation.History (process.observation initial) (process.observation after) := by
  let retainedHistory : Approximation.Observation.History (process.observation initial) older.generic :=
    older.genericEq.symm ▸ history
  have refines : Approximation.Observation.Refines newer.generic older.generic := by
    have canonical : Approximation.Observation.Refines (process.observation after) (process.observation before) :=
      afterEq.symm ▸ process.refine_observation before target positive
    exact newer.genericEq.symm ▸ older.genericEq.symm ▸ canonical
  let next : Approximation.Observation.History (process.observation initial) newer.generic :=
    .step retainedHistory refines
  exact newer.genericEq ▸ next

end Observation

/-- The actual final process witness satisfies the initial possibility predicate of its finite history. -/
theorem history_witness_possible (process : Gaussian.Process)
    {initial current : process.State}
    (history : Approximation.Observation.History
      (process.observation initial) (process.observation current)) :
    process.Possible initial (process.witness current).val :=
  history.latest_witness_possible_initial

end Purelib.Approximation.Gaussian.Process

end
