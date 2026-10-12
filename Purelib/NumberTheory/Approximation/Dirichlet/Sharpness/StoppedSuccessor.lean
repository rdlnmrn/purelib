module
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.List.Event
public import Purelib.Geometry.Rational.Box.Content
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Measure.Distribution.Markov.Block
import Purelib.Measure.Distribution.Markov.Path.Basic
public import Purelib.NumberTheory.Approximation.Best.Successor.Dynamics
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BoxDynamics
public import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.FiniteDynamics
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Robust sharpness along stopped finite successor dynamics

Every displayed rational source in the robust critical box has each selected
critical pair as a genuine consecutive-level state.  Starting from any state
of that source's finite transversal, coefficient-local successor dynamics
strictly raises denominator quadrance until its explicit terminal reset.  We
stop at the selected critical state, so the source-denominator rank gives a
uniform probability-one finite block return.

The stopped seed hold and terminal regeneration are explicit boundary edges;
they are not claimed to belong to the unrestarted continued-fraction map.
All other transition atoms are proved genuine local successors.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.StoppedSuccessor

/-- At every rational source inside the robust box, a selected critical
window is a genuine state of that source's finite successor transversal. -/
@[expose] def robustSeedState
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : GaussianInt.Fraction)
    (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count) : Best.Successor.Dynamics.State source :=
  { previous :=
      (Dirichlet.Critical.Run.badWindowAtOffset
        certificate requestedScale count offset).1.lower
    current :=
      (Dirichlet.Critical.Run.badWindowAtOffset
        certificate requestedScale count offset).1.upper
    consecutive :=
      Dirichlet.Critical.Robust.Run.robustRunBox_consecutiveAtOffset
        certificate requestedScale count source.value inside offset }

/-- The stopped seed event uniformly realizes a genuine bad window at the
displayed source, not merely at the box anchor. -/
@[expose] def robustSuccessorRegion
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : GaussianInt.Fraction)
    (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count) :
    Dirichlet.Sharpness.FiniteDynamics.BadWindowRegion
      (Best.Successor.Dynamics.State source) threshold requestedScale where
  event := Best.Successor.Dynamics.seedEvent
    (Dirichlet.Sharpness.StoppedSuccessor.robustSeedState certificate requestedScale count source inside offset)
  realize := by
    intro state selected
    have stateIdentity :=
      (Best.Successor.Dynamics.seedEvent_eq_true_iff
        (Dirichlet.Sharpness.StoppedSuccessor.robustSeedState certificate requestedScale count source inside offset)
        state).mp selected
    subst state
    exact
      { source := source
        lower :=
          (Dirichlet.Critical.Run.badWindowAtOffset
            certificate requestedScale count offset).1.lower
        upper :=
          (Dirichlet.Critical.Run.badWindowAtOffset
            certificate requestedScale count offset).1.upper
        beyondScale :=
          (Dirichlet.Critical.Run.badWindowAtOffset
            certificate requestedScale count offset).1.beyondScale
        consecutive :=
          Dirichlet.Critical.Robust.Run.robustRunBox_consecutiveAtOffset
            certificate requestedScale count source.value inside offset
        violates :=
          Dirichlet.Critical.Robust.Run.robustRunBox_violationAtOffset
            certificate requestedScale count source.value inside offset }

/-- Exact probability of seeing the selected robust critical state at one of
the next displayed stopped-successor block endpoints. -/
@[expose] def robustSuccessorReturnProbability
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : GaussianInt.Fraction)
    (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count)
    (initial : Measure.Distribution (Best.Successor.Dynamics.State source))
    (burnIn blockCount : Nat) : Fraction.Rational :=
  let seed := Dirichlet.Sharpness.StoppedSuccessor.robustSeedState certificate requestedScale count source inside
    offset
  let transition := Best.Successor.Dynamics.stoppedTransition seed
  let region := Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorRegion certificate requestedScale count source
    inside offset
  (Measure.markovPaths
    (Measure.Distribution.blockTransition transition
      (GaussianInt.normNat
        source.denominator + 1))
    blockCount
    (Measure.Distribution.iterate transition burnIn initial)).probability
      (Data.List.pathHits region.event)

/-- Quantitative finite return theorem for the stopped genuine-successor
kernel.  Its block length is the displayed source-denominator quadrance plus
one and its exact uniform rate is one. -/
theorem robustSuccessorReturnProbability_lower
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : GaussianInt.Fraction)
    (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count)
    (initial : Measure.Distribution (Best.Successor.Dynamics.State source))
    (burnIn blockCount : Nat) :
    1 - (1 - 1) ^ blockCount ≤
      Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability certificate requestedScale count source
        inside offset initial burnIn blockCount := by
  let seed := Dirichlet.Sharpness.StoppedSuccessor.robustSeedState certificate requestedScale count source inside
    offset
  let transition := Best.Successor.Dynamics.stoppedTransition seed
  let region := Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorRegion certificate requestedScale count source
    inside offset
  have lower := region.block_pathHit_probability_lower initial transition
    (Best.Successor.Dynamics.stoppedBlockHitCertificate seed)
    burnIn blockCount
  simpa only [Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability, seed, transition, region,
    Best.Successor.Dynamics.stoppedBlockLength,
    Best.Successor.Dynamics.stoppedBlockRate] using lower

/-- With at least one displayed return block, the hit probability is exactly
one.  This is finite absorption, not an almost-everywhere recurrence claim. -/
theorem robustSuccessorReturnProbability_eq_one
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : GaussianInt.Fraction)
    (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count)
    (initial : Measure.Distribution (Best.Successor.Dynamics.State source))
    (burnIn blockCount : Nat) (blockCountPositive : 0 < blockCount) :
    Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability certificate requestedScale count source
      inside offset initial burnIn blockCount = 1 := by
  have lower := Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability_lower certificate
    requestedScale count source inside offset initial burnIn blockCount
  have blockCountNonzero : blockCount ≠ 0 := Nat.ne_of_gt blockCountPositive
  have oneLower : (1 : Fraction.Rational) ≤
      Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability certificate requestedScale count source
        inside offset initial burnIn blockCount := by
    simpa only [sub_self, zero_pow blockCountNonzero, sub_eq_add_neg, neg_zero, add_zero] using lower
  exact le_antisymm
    (Measure.Distribution.probability_le_one _ _)
    oneLower

/-- Constructive soundness of a selected path hit: the result is the actual
bad-window record at the displayed rational source. -/
@[expose] def badWindow_of_robustSuccessor_pathHits
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : GaussianInt.Fraction)
    (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count) (path : List (Best.Successor.Dynamics.State source))
    (hits : Data.List.pathHits
      (Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorRegion certificate requestedScale count source inside
        offset).event path = true) :
    BadWindow threshold requestedScale :=
  (Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorRegion certificate requestedScale count source inside
    offset).badWindow_of_pathHits path hits

/-- Consolidated finite Chevallier analogue: the critical source box is
proper and has positive exact content, and every displayed rational source in
it has probability-one stopped-successor return to every selected critical
run offset after any burn-in and one or more displayed blocks. -/
theorem chevallierAnalogue
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (Dirichlet.Critical.Robust.Run.robustRunBox
        certificate requestedScale count).Proper ∧
      0 < Geometry.Rational.Box.Content.boxContent
        (Dirichlet.Critical.Robust.Run.robustRunBox
          certificate requestedScale count) ∧
      ∀ (source : GaussianInt.Fraction),
        (inside : (Dirichlet.Critical.Robust.Run.robustRunBox
          certificate requestedScale count).Contains source.value) →
        ∀ (offset : Fin count)
          (initial : Measure.Distribution (Best.Successor.Dynamics.State source))
          (burnIn blockCount : Nat),
          0 < blockCount →
          Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability certificate requestedScale count
            source inside offset initial burnIn blockCount = 1 := by
  refine ⟨Dirichlet.Critical.Robust.Run.robustRunBox_proper
      certificate requestedScale count,
    Dirichlet.Sharpness.BoxDynamics.robustRunBox_content_pos
      certificate requestedScale count, ?_⟩
  intro source inside offset initial burnIn blockCount blockCountPositive
  exact Dirichlet.Sharpness.StoppedSuccessor.robustSuccessorReturnProbability_eq_one certificate requestedScale
    count source inside offset initial burnIn blockCount blockCountPositive

end Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.StoppedSuccessor

end
