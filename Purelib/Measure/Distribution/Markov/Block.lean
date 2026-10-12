module

import Purelib.Measure.Distribution.Markov.Path.Avoidance
public import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Markov.Path.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
/-!
# Finite Markov return estimates

This module gives an executable finite substitute for the recurrence step in
an ergodic argument.  A finite Markov path records exactly a supplied number
of future states.  If every current state has at least a displayed rational
chance `rate` to enter an event at the next step, then the probability of
avoiding the event for `count` steps is at most `(1 - rate) ^ count`.

The block form applies the same argument to an explicitly iterated transition
after any supplied burn-in time.  It is therefore suitable for a finite
transversal model: the geometry must provide a uniform block-hit certificate,
while this file performs the probability and recurrence calculation.  There
is no infinite path, stationary process, limit, or appeal to ergodicity.
-/

public section

namespace Purelib.Measure
namespace Distribution

/-- Advance the exact transition kernel by the supplied block length from a point mass at the original state. -/
@[expose] def blockTransition {alpha : Type}
    (transition : alpha → Distribution alpha) (blockLength : Nat)
    (item : alpha) : Distribution alpha :=
  Distribution.iterate transition blockLength (Distribution.pure item)

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a positive block length and positive uniform lower bound on endpoint event probability.

The same rate, no greater than one, applies to the original kernel's exact block transition from every supplied state.
-/
structure UniformBlockHitCertificate {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool) where
  /-- The retained number of original transition steps in each block. -/ blockLength : Nat
  /-- The exact retained block length is positive. -/ blockLengthPositive : 0 < blockLength
  /-- The retained rational lower bound on endpoint hit probability. -/ rate : Fraction.Rational
  /-- The exact retained hit rate is positive. -/ ratePositive : 0 < rate
  /-- The retained hit rate is at most one. -/ rateAtMostOne : rate ≤ 1
  /-- Every original starting state has endpoint hit probability at least the retained rate after the exact block
    length. -/ endpointHitLower : ∀ item,
    rate ≤ (blockTransition transition blockLength item).probability event

constructive_injectivity UniformBlockHitCertificate

namespace UniformBlockHitCertificate

open Purelib
/-- After any retained burn-in, avoiding the event at all sampled block endpoints has probability at most the geometric
allowance. -/
theorem avoidanceProbability_le_pow {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    (certificate : UniformBlockHitCertificate transition event)
    (source : Distribution alpha) (burnIn blockCount : Nat) :
    (markovPaths
        (blockTransition transition certificate.blockLength)
        blockCount (Distribution.iterate transition burnIn source)).probability
          (Data.List.pathAvoids event) ≤
      (1 - certificate.rate) ^ blockCount := by
  exact markovPaths_probability_pathAvoids_le_pow
    (blockTransition transition certificate.blockLength) event
    certificate.rate certificate.ratePositive.le certificate.rateAtMostOne
    certificate.endpointHitLower blockCount
    (Distribution.iterate transition burnIn source)

/-- After any retained burn-in, hitting the event at a sampled block endpoint has probability at least the complementary
geometric allowance. -/
theorem hitProbability_lower {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    (certificate : UniformBlockHitCertificate transition event)
    (source : Distribution alpha) (burnIn blockCount : Nat) :
    1 - (1 - certificate.rate) ^ blockCount ≤
      (markovPaths
        (blockTransition transition certificate.blockLength)
        blockCount (Distribution.iterate transition burnIn source)).probability
          (Data.List.pathHits event) := by
  exact markovPaths_probability_pathHits_lower
    (blockTransition transition certificate.blockLength) event
    certificate.rate certificate.ratePositive.le certificate.rateAtMostOne
    certificate.endpointHitLower blockCount
    (Distribution.iterate transition burnIn source)

end UniformBlockHitCertificate

end Distribution

end Purelib.Measure

end
