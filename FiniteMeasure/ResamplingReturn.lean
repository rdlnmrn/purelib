import mathlib.Tactic.QuotientFreeOmega
import FiniteMeasure.Stationary

/-!
# Independent finite resampling as an exact stationary return model

Repeatedly replacing the current state by a fresh sample from one displayed
rational law is an executable finite Markov transition.  The law is exactly
stationary, and every positive-probability event has a one-step uniform
return certificate at precisely its displayed mass.  This supplies a useful
fully discharged model for the generic finite recurrence interfaces.
-/

namespace FiniteMeasure

namespace Distribution

/-- One transition discards the current state and samples the displayed law. -/
def resamplingTransition {alpha : Type} (law : Distribution alpha)
    (_item : alpha) : Distribution alpha :=
  law

/-- The resampled law is exactly stationary for its own constant transition. -/
theorem resampling_stationary {alpha : Type} (law : Distribution alpha) :
    law.StationaryFor (resamplingTransition law) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  unfold Distribution.step resamplingTransition
  rw [law.bind_expectation, law.expectation_constant]

/-- A positive event under a displayed law is reached with its exact mass in
one independent resampling step, uniformly from every current state. -/
def resamplingBlockHitCertificate {alpha : Type} (law : Distribution alpha)
    (event : alpha → Bool) (positive : 0 < law.probability event) :
    UniformBlockHitCertificate (resamplingTransition law) event := by
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
    ((Distribution.pure item).bind (resamplingTransition law)).probability event
  rw [(Distribution.pure_bind_evaluationEquivalent item
    (resamplingTransition law)).probability_eq event]
  exact le_rfl

/-- Consequently, after any supplied burn-in, the next displayed resampling
blocks hit the event with probability at least the exact geometric bound. -/
theorem resampling_pathHit_probability_lower {alpha : Type}
    (law : Distribution alpha) (event : alpha → Bool)
    (positive : 0 < law.probability event) (source : Distribution alpha)
    (burnIn blockCount : Nat) :
    1 - (1 - law.probability event) ^ blockCount ≤
      (markovPaths
        (blockTransition (resamplingTransition law) 1)
        blockCount
        (Distribution.iterate (resamplingTransition law) burnIn source)).probability
          (pathHits event) := by
  exact (resamplingBlockHitCertificate law event positive).hitProbability_lower
    source burnIn blockCount

end Distribution

end FiniteMeasure
