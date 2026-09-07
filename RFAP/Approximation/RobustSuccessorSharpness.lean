import RFAP.Approximation.RobustDynamicalSharpness
import RFAP.Approximation.SuccessorDynamics

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

namespace RFAP.RobustSuccessorSharpness

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev State := RFAP.SuccessorDynamics.State
abbrev BadWindow := RFAP.DynamicalSharpness.BadWindow

open RFAP.BestApproximation

/-- At every rational source inside the robust box, a selected critical
window is a genuine state of that source's finite successor transversal. -/
def robustSeedState
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : Fraction)
    (inside : (RFAP.RobustCriticalRun.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count) : State source :=
  { previous :=
      (RFAP.CriticalBadWindowRun.badWindowAtOffset
        certificate requestedScale count offset).1.lower
    current :=
      (RFAP.CriticalBadWindowRun.badWindowAtOffset
        certificate requestedScale count offset).1.upper
    consecutive :=
      RFAP.RobustCriticalRun.robustRunBox_consecutiveAtOffset
        certificate requestedScale count source.value inside offset }

/-- The stopped seed event uniformly realizes a genuine bad window at the
displayed source, not merely at the box anchor. -/
def robustSuccessorRegion
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : Fraction)
    (inside : (RFAP.RobustCriticalRun.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count) :
    RFAP.DynamicalSharpness.BadWindowRegion
      (State source) threshold requestedScale where
  event := RFAP.SuccessorDynamics.seedEvent
    (robustSeedState certificate requestedScale count source inside offset)
  realize := by
    intro state selected
    have stateIdentity :=
      (RFAP.SuccessorDynamics.seedEvent_eq_true_iff
        (robustSeedState certificate requestedScale count source inside offset)
        state).mp selected
    subst state
    exact
      { source := source
        lower :=
          (RFAP.CriticalBadWindowRun.badWindowAtOffset
            certificate requestedScale count offset).1.lower
        upper :=
          (RFAP.CriticalBadWindowRun.badWindowAtOffset
            certificate requestedScale count offset).1.upper
        beyondScale :=
          (RFAP.CriticalBadWindowRun.badWindowAtOffset
            certificate requestedScale count offset).1.beyondScale
        consecutive :=
          RFAP.RobustCriticalRun.robustRunBox_consecutiveAtOffset
            certificate requestedScale count source.value inside offset
        violates :=
          RFAP.RobustCriticalRun.robustRunBox_violationAtOffset
            certificate requestedScale count source.value inside offset }

/-- Exact probability of seeing the selected robust critical state at one of
the next displayed stopped-successor block endpoints. -/
def robustSuccessorReturnProbability
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : Fraction)
    (inside : (RFAP.RobustCriticalRun.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count)
    (initial : _root_.FiniteMeasure.Distribution (State source))
    (burnIn blockCount : Nat) : Coordinate :=
  let seed := robustSeedState certificate requestedScale count source inside
    offset
  let transition := RFAP.SuccessorDynamics.stoppedTransition seed
  let region := robustSuccessorRegion certificate requestedScale count source
    inside offset
  (_root_.FiniteMeasure.markovPaths
    (_root_.FiniteMeasure.Distribution.blockTransition transition
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        source.denominator + 1))
    blockCount
    (_root_.FiniteMeasure.Distribution.iterate transition burnIn initial)).probability
      (_root_.FiniteMeasure.pathHits region.event)

/-- Quantitative finite return theorem for the stopped genuine-successor
kernel.  Its block length is the displayed source-denominator quadrance plus
one and its exact uniform rate is one. -/
theorem robustSuccessorReturnProbability_lower
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : Fraction)
    (inside : (RFAP.RobustCriticalRun.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count)
    (initial : _root_.FiniteMeasure.Distribution (State source))
    (burnIn blockCount : Nat) :
    1 - (1 - 1) ^ blockCount ≤
      robustSuccessorReturnProbability certificate requestedScale count source
        inside offset initial burnIn blockCount := by
  let seed := robustSeedState certificate requestedScale count source inside
    offset
  let transition := RFAP.SuccessorDynamics.stoppedTransition seed
  let region := robustSuccessorRegion certificate requestedScale count source
    inside offset
  have lower := region.block_pathHit_probability_lower initial transition
    (RFAP.SuccessorDynamics.stoppedBlockHitCertificate seed)
    burnIn blockCount
  simpa only [robustSuccessorReturnProbability, seed, transition, region,
    RFAP.SuccessorDynamics.stoppedBlockLength,
    RFAP.SuccessorDynamics.stoppedBlockRate] using lower

/-- With at least one displayed return block, the hit probability is exactly
one.  This is finite absorption, not an almost-everywhere recurrence claim. -/
theorem robustSuccessorReturnProbability_eq_one
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : Fraction)
    (inside : (RFAP.RobustCriticalRun.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count)
    (initial : _root_.FiniteMeasure.Distribution (State source))
    (burnIn blockCount : Nat) (blockCountPositive : 0 < blockCount) :
    robustSuccessorReturnProbability certificate requestedScale count source
      inside offset initial burnIn blockCount = 1 := by
  have lower := robustSuccessorReturnProbability_lower certificate
    requestedScale count source inside offset initial burnIn blockCount
  have blockCountNonzero : blockCount ≠ 0 := Nat.ne_of_gt blockCountPositive
  have oneLower : (1 : Coordinate) ≤
      robustSuccessorReturnProbability certificate requestedScale count source
        inside offset initial burnIn blockCount := by
    simpa only [sub_self, zero_pow blockCountNonzero, sub_zero] using lower
  exact le_antisymm
    (_root_.FiniteMeasure.Distribution.probability_le_one _ _)
    oneLower

/-- Constructive soundness of a selected path hit: the result is the actual
bad-window record at the displayed rational source. -/
def badWindow_of_robustSuccessor_pathHits
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (source : Fraction)
    (inside : (RFAP.RobustCriticalRun.robustRunBox
      certificate requestedScale count).Contains source.value)
    (offset : Fin count) (path : List (State source))
    (hits : _root_.FiniteMeasure.pathHits
      (robustSuccessorRegion certificate requestedScale count source inside
        offset).event path = true) :
    BadWindow threshold requestedScale :=
  (robustSuccessorRegion certificate requestedScale count source inside
    offset).badWindow_of_pathHits path hits

/-- Consolidated finite Chevallier analogue: the critical source box is
proper and has positive exact content, and every displayed rational source in
it has probability-one stopped-successor return to every selected critical
run offset after any burn-in and one or more displayed blocks. -/
theorem finiteChevallierAnalogue
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (RFAP.RobustCriticalRun.robustRunBox
        certificate requestedScale count).Proper ∧
      0 < RFAP.FiniteMeasure.boxContent
        (RFAP.RobustCriticalRun.robustRunBox
          certificate requestedScale count) ∧
      ∀ (source : Fraction),
        (inside : (RFAP.RobustCriticalRun.robustRunBox
          certificate requestedScale count).Contains source.value) →
        ∀ (offset : Fin count)
          (initial : _root_.FiniteMeasure.Distribution (State source))
          (burnIn blockCount : Nat),
          0 < blockCount →
          robustSuccessorReturnProbability certificate requestedScale count
            source inside offset initial burnIn blockCount = 1 := by
  refine ⟨RFAP.RobustCriticalRun.robustRunBox_proper
      certificate requestedScale count,
    RFAP.RobustDynamicalSharpness.robustRunBox_content_pos
      certificate requestedScale count, ?_⟩
  intro source inside offset initial burnIn blockCount blockCountPositive
  exact robustSuccessorReturnProbability_eq_one certificate requestedScale
    count source inside offset initial burnIn blockCount blockCountPositive

end RFAP.RobustSuccessorSharpness
