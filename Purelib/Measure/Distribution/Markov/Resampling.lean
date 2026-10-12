module
import Purelib.Data.List.Event

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Markov.Block
import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Markov.Stationary.Basic
import Purelib.Measure.Distribution.Markov.Path.Basic
import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

/-!
# Independent finite resampling as an exact stationary return model

Repeatedly replacing the current state by a fresh sample from one displayed
rational law is an executable finite Markov transition.  The law is exactly
stationary, and every positive-probability event has a one-step uniform
return certificate at precisely its displayed mass.  This supplies a useful
fully discharged model for the generic finite recurrence interfaces.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

/-- Return the same exact retained distribution from every input state. -/
def resamplingTransition {alpha : Type} (law : Distribution alpha)
    (_item : alpha) : Distribution alpha :=
  law

section
open Purelib.Measure
/-- The retained law is stationary for its own constant resampling kernel. -/
theorem resampling_stationary {alpha : Type} (law : Distribution alpha) :
    law.StationaryFor (Distribution.resamplingTransition law) := by
  apply Distribution.EvaluationEquivalent.of_expectation_eq
  intro value
  unfold Distribution.step Distribution.resamplingTransition
  rw [law.bind_expectation, law.expectation_constant]

/-- Construct a one-step uniform hit certificate using the exact retained resampling event probability.

The supplied positive-probability witness makes that original probability the retained positive rate from every starting
state. -/
def resamplingBlockHitCertificate {alpha : Type} (law : Distribution alpha)
    (event : alpha → Bool) (positive : 0 < law.probability event) :
    UniformBlockHitCertificate (Distribution.resamplingTransition law) event := by
  refine
    { blockLength := 1
      blockLengthPositive := by decide
      rate := law.probability event
      ratePositive := positive
      rateAtMostOne := law.probability_le_one event
      endpointHitLower := ?_ }
  intro item
  unfold blockTransition
  change law.probability event ≤
    ((Distribution.pure item).bind (Distribution.resamplingTransition law)).probability event
  rw [(Distribution.pure_bind_evaluationEquivalent item
    (Distribution.resamplingTransition law)).probability_eq event]
  exact le_rfl

end

open Purelib in
open Purelib.Measure in
/-- After any burn-in, repeated resampling has the complementary geometric hit lower bound at the exact event
probability. -/
theorem resampling_pathHit_probability_lower {alpha : Type}
    (law : Distribution alpha) (event : alpha → Bool)
    (positive : 0 < law.probability event) (source : Distribution alpha)
    (burnIn blockCount : Nat) :
    1 - (1 - law.probability event) ^ blockCount ≤
      (markovPaths
        (blockTransition (Distribution.resamplingTransition law) 1)
        blockCount
        (Distribution.iterate (Distribution.resamplingTransition law) burnIn source)).probability
          (Data.List.pathHits event) := by
  exact (Distribution.resamplingBlockHitCertificate law event positive).hitProbability_lower
    source burnIn blockCount

end Distribution

end Purelib.Measure
