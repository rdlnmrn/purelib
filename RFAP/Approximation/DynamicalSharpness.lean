import RFAP.Approximation.FiniteWindowSharpness
import FiniteMeasure.Stationary

/-!
# Finite dynamical Dirichlet-window sharpness

This module states the finite dynamical interface needed for a constructive
analogue of Chevallier's almost-everywhere sharpness argument.  A bad window
contains a displayed rational source, two displayed Gaussian-integral pairs,
their consecutive-best certificate, a strict scale inequality, and the
failure of a proposed sharper threshold.

A Boolean region in an arbitrary finite dynamical state space is sound when
every selected state constructs such a bad window.  The finite stationary
occupation and uniform block-return theorems then give quantitative lower
probabilities of reaching a sound region after a supplied finite burn-in.
No completed complex input, infinite minimal-vector sequence, Haar space,
limit, or ergodic theorem is introduced here.
-/

namespace RFAP.DynamicalSharpness

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation
open RFAP.HurwitzApproximation

/-- Fully displayed counterexample to one proposed sharper Dirichlet-window
threshold beyond one supplied natural scale. -/
structure BadWindow (threshold : Coordinate) (requestedScale : Nat) where
  source : Fraction
  lower : Pair
  upper : Pair
  beyondScale : requestedScale < denominatorQuadrance upper
  consecutive : AreConsecutiveBest source.value lower upper
  violates : 1 < threshold *
    dirichletWindowQuadrance source.value lower upper

/-- The existing Pell construction, repackaged as explicit bad-window data. -/
def criticalBadWindow {threshold : Coordinate}
    (certificate : RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale : Nat) : BadWindow threshold requestedScale := by
  let stage := RFAP.FiniteWindowSharpness.sharpnessStage
    threshold requestedScale
  exact
    { source := RFAP.FiniteWindowSharpness.criticalSource stage
      lower := RFAP.FiniteWindowSharpness.criticalLowerPair stage
      upper := RFAP.FiniteWindowSharpness.criticalUpperPair stage
      beyondScale := by
        simpa only [stage] using
          RFAP.FiniteWindowSharpness.requestedScale_lt_criticalUpperDenominatorQuadrance
            threshold requestedScale
      consecutive :=
        RFAP.FiniteWindowSharpness.criticalPairs_areConsecutiveBest stage
      violates := by
        simpa only [stage] using
          RFAP.FiniteWindowSharpness.one_lt_sharperThreshold_mul_criticalWindow
            certificate requestedScale }

/-- A finite dynamical region whose every selected state constructs a bad
window at the requested threshold and scale. -/
structure BadWindowRegion (state : Type) (threshold : Coordinate)
    (requestedScale : Nat) where
  event : state → Bool
  realize : ∀ item, event item = true → BadWindow threshold requestedScale

namespace BadWindowRegion

/-- A displayed finite path that hits a sound region constructively returns
one bad-window witness. -/
def badWindow_of_pathHits {state : Type} {threshold : Coordinate}
    {requestedScale : Nat}
    (region : BadWindowRegion state threshold requestedScale) :
    ∀ path : List state,
      _root_.FiniteMeasure.pathHits region.event path = true →
        BadWindow threshold requestedScale
  | [], selected => by
      simp only [_root_.FiniteMeasure.pathHits,
        _root_.FiniteMeasure.pathAvoids,
        _root_.FiniteMeasure.complementEvent, Bool.not_true] at selected
      cases selected
  | item :: remaining, selected => by
      cases hit : region.event item
      · apply region.badWindow_of_pathHits remaining
        simpa only [_root_.FiniteMeasure.pathHits,
          _root_.FiniteMeasure.pathAvoids,
          _root_.FiniteMeasure.complementEvent, hit, Bool.not_false,
          Bool.true_and] using selected
      · exact region.realize item hit

/-- A stationary finite state law and an exact occupation-variance bound give
a quantitative lower probability of constructing a bad window.  Soundness
is supplied by `badWindow_of_pathHits`; the inequality is the finite
mean-ergodic recurrence estimate. -/
theorem stationary_pathHit_probability_lower {state : Type}
    {threshold : Coordinate} {requestedScale : Nat}
    (region : BadWindowRegion state threshold requestedScale)
    (distribution : _root_.FiniteMeasure.Distribution state)
    (transition : state → _root_.FiniteMeasure.Distribution state)
    (stationary : distribution.StationaryFor transition)
    (regionPositive : 0 < distribution.probability region.event)
    (count : Nat) (countPositive : 0 < (count : Coordinate)) :
    1 - (_root_.FiniteMeasure.markovPaths transition count distribution).variance
          (_root_.FiniteMeasure.pathVisitFrequency count region.event) /
          distribution.probability region.event ^ 2 ≤
      (_root_.FiniteMeasure.markovPaths transition count distribution).probability
        (_root_.FiniteMeasure.pathHits region.event) :=
  stationary.pathHit_probability_lower_of_variance region.event
    regionPositive count countPositive

/-- A uniform finite block-return certificate gives a quantitative lower
probability of constructing a bad window after any supplied burn-in. -/
theorem block_pathHit_probability_lower {state : Type}
    {threshold : Coordinate} {requestedScale : Nat}
    (region : BadWindowRegion state threshold requestedScale)
    (distribution : _root_.FiniteMeasure.Distribution state)
    (transition : state → _root_.FiniteMeasure.Distribution state)
    (returnCertificate :
      _root_.FiniteMeasure.Distribution.UniformBlockHitCertificate
        transition region.event)
    (burnIn blockCount : Nat) :
    1 - (1 - returnCertificate.rate) ^ blockCount ≤
      (_root_.FiniteMeasure.markovPaths
        (_root_.FiniteMeasure.Distribution.blockTransition transition
          returnCertificate.blockLength)
        blockCount
        (_root_.FiniteMeasure.Distribution.iterate transition burnIn
          distribution)).probability
        (_root_.FiniteMeasure.pathHits region.event) :=
  returnCertificate.hitProbability_lower distribution burnIn blockCount

end BadWindowRegion

end RFAP.DynamicalSharpness
