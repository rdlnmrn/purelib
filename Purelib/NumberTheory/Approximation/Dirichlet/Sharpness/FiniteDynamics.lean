module

import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Iteration
public import Purelib.Measure.Distribution.Markov.Block
import Purelib.Measure.Distribution.Markov.Path.Basic
public import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Weighted.Event
public import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
public import Purelib.Measure.Distribution.Markov.Stationary.Basic
import Purelib.Measure.Distribution.Markov.Stationary.Occupation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Moments.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

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

namespace Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.FiniteDynamics

set_option genInjectivity false in
/-- A finite dynamical region whose every selected state constructs a bad
window at the requested threshold and scale. -/
structure BadWindowRegion (state : Type) (threshold : Fraction.Rational)
    (requestedScale : Nat) where
  /-- The decidable state event selecting the finite bad-window region. -/ event : state → Bool
  /-- Construct a bad window at the retained threshold and scale from each selected state. -/ realize : ∀ item, event
    item = true → BadWindow threshold requestedScale

constructive_injectivity BadWindowRegion

namespace BadWindowRegion

/-- A displayed finite path that hits a sound region constructively returns
one bad-window witness. -/
@[expose] def badWindow_of_pathHits {state : Type} {threshold : Fraction.Rational}
    {requestedScale : Nat}
    (region : Dirichlet.Sharpness.FiniteDynamics.BadWindowRegion state threshold requestedScale) :
    ∀ path : List state,
      Data.List.pathHits region.event path = true →
        BadWindow threshold requestedScale
  | [], selected => by
      simp only [Data.List.pathHits,
        Data.List.pathAvoids,
        Measure.complementEvent, Bool.not_true] at selected
      cases selected
  | item :: remaining, selected => by
      cases hit : region.event item
      · apply region.badWindow_of_pathHits remaining
        simpa only [Data.List.pathHits,
          Data.List.pathAvoids,
          Measure.complementEvent, hit, Bool.not_false,
          Bool.true_and] using selected
      · exact region.realize item hit

/-- A stationary finite state law and an exact occupation-variance bound give
a quantitative lower probability of constructing a bad window.  Soundness
is supplied by `badWindow_of_pathHits`; the inequality is the finite
mean-ergodic recurrence estimate. -/
theorem stationary_pathHit_probability_lower {state : Type}
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (region : Dirichlet.Sharpness.FiniteDynamics.BadWindowRegion state threshold requestedScale)
    (distribution : Measure.Distribution state)
    (transition : state → Measure.Distribution state)
    (stationary : distribution.StationaryFor transition)
    (regionPositive : 0 < distribution.probability region.event)
    (count : Nat) (countPositive : 0 < (count : Fraction.Rational)) :
    1 - (Measure.markovPaths transition count distribution).variance
          (Measure.pathVisitFrequency count region.event) /
          distribution.probability region.event ^ 2 ≤
      (Measure.markovPaths transition count distribution).probability
        (Data.List.pathHits region.event) :=
  stationary.pathHit_probability_lower_of_variance region.event
    regionPositive count countPositive

/-- A uniform finite block-return certificate gives a quantitative lower
probability of constructing a bad window after any supplied burn-in. -/
theorem block_pathHit_probability_lower {state : Type}
    {threshold : Fraction.Rational} {requestedScale : Nat}
    (region : Dirichlet.Sharpness.FiniteDynamics.BadWindowRegion state threshold requestedScale)
    (distribution : Measure.Distribution state)
    (transition : state → Measure.Distribution state)
    (returnCertificate :
      Measure.Distribution.UniformBlockHitCertificate
        transition region.event)
    (burnIn blockCount : Nat) :
    1 - (1 - returnCertificate.rate) ^ blockCount ≤
      (Measure.markovPaths
        (Measure.Distribution.blockTransition transition
          returnCertificate.blockLength)
        blockCount
        (Measure.Distribution.iterate transition burnIn
          distribution)).probability
        (Data.List.pathHits region.event) :=
  returnCertificate.hitProbability_lower distribution burnIn blockCount

end BadWindowRegion

end Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.FiniteDynamics

end
