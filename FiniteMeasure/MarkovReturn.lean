import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Dynamics

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

namespace FiniteMeasure

/-- Distribution of exactly `count` future states of a finite Markov chain,
starting from one displayed current state.  The current state itself is not
included in the returned list. -/
def markovPathFrom {alpha : Type}
    (transition : alpha → Distribution alpha) :
    Nat → alpha → Distribution (List alpha)
  | 0, _ => Distribution.pure []
  | count + 1, item =>
      (transition item).bind fun next =>
        (markovPathFrom transition count next).map fun remaining =>
          next :: remaining

/-- Distribution of exactly `count` future states from a displayed finite
initial law. -/
def markovPaths {alpha : Type} (transition : alpha → Distribution alpha)
    (count : Nat) (source : Distribution alpha) : Distribution (List alpha) :=
  source.bind (markovPathFrom transition count)

/-- Executable event that no entry of a displayed path belongs to `event`. -/
def pathAvoids {alpha : Type} (event : alpha → Bool) :
    List alpha → Bool
  | [] => true
  | item :: remaining => !(event item) && pathAvoids event remaining

/-- Executable event that a displayed path visits `event` at least once. -/
def pathHits {alpha : Type} (event : alpha → Bool) :
    List alpha → Bool :=
  complementEvent (pathAvoids event)

/-- Exact recursively evaluated probability of avoiding `event` for the next
`count` states, conditional on one current state. -/
def markovAvoidanceProbability {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool) :
    Nat → alpha → Coordinate
  | 0, _ => 1
  | count + 1, item =>
      (transition item).expectation fun next =>
        Distribution.indicator (complementEvent event) next *
          markovAvoidanceProbability transition event count next

namespace Distribution

/-- The recursive avoidance calculation is exactly the probability of the
corresponding displayed finite Markov path event. -/
theorem markovPathFrom_probability_pathAvoids {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (count : Nat) (item : alpha) :
    (markovPathFrom transition count item).probability (pathAvoids event) =
      markovAvoidanceProbability transition event count item := by
  induction count generalizing item with
  | zero =>
      change (Distribution.pure ([] : List alpha)).probability
          (pathAvoids event) = 1
      rw [pure_probability]
      rfl
  | succ count inductionHypothesis =>
      rw [markovPathFrom, bind_probability]
      unfold markovAvoidanceProbability
      exact (transition item).expectation_congr _ _ (fun next => by
        rw [(markovPathFrom transition count next).map_probability]
        cases selected : event next
        · calc
            (markovPathFrom transition count next).probability
                  (fun remaining => pathAvoids event (next :: remaining)) =
                (markovPathFrom transition count next).probability
                  (pathAvoids event) :=
              (markovPathFrom transition count next).probability_congr _ _
                (fun remaining => by
                  simp only [pathAvoids, selected, Bool.not_false,
                    Bool.true_and])
            _ = markovAvoidanceProbability transition event count next :=
              inductionHypothesis next
            _ = Distribution.indicator (complementEvent event) next *
                  markovAvoidanceProbability transition event count next := by
              simp only [complementEvent, selected, Bool.not_false,
                Distribution.indicator, one_mul]
        · calc
            (markovPathFrom transition count next).probability
                  (fun remaining => pathAvoids event (next :: remaining)) =
                (markovPathFrom transition count next).probability
                  (fun _ => false) :=
              (markovPathFrom transition count next).probability_congr _ _
                (fun remaining => by
                  simp only [pathAvoids, selected, Bool.not_true,
                    Bool.false_and])
            _ = 0 :=
              (markovPathFrom transition count next).probability_false
            _ = Distribution.indicator (complementEvent event) next *
                  markovAvoidanceProbability transition event count next := by
              simp only [complementEvent, selected, Bool.not_true,
                Distribution.indicator, zero_mul])

/-- Avoidance probability for a finite initial law is the expectation of the
statewise recursive avoidance calculation. -/
theorem markovPaths_probability_pathAvoids {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (count : Nat) (source : Distribution alpha) :
    (markovPaths transition count source).probability (pathAvoids event) =
      source.expectation
        (markovAvoidanceProbability transition event count) := by
  rw [markovPaths, bind_probability]
  exact source.expectation_congr _ _ (fun item =>
    markovPathFrom_probability_pathAvoids transition event count item)

/-- A uniform one-step hit chance gives geometric avoidance decay from every
displayed current state. -/
theorem markovAvoidanceProbability_le_pow {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rate : Coordinate) (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (hitLower : ∀ item, rate ≤ (transition item).probability event) :
    ∀ (count : Nat) (item : alpha),
      markovAvoidanceProbability transition event count item ≤
        (1 - rate) ^ count
  | 0, item => le_rfl
  | count + 1, item => by
      have allowanceNonnegative : 0 ≤ (1 - rate) ^ count :=
        RFAP.ConstructiveFraction.pow_nonneg_direct
          (RFAP.ConstructiveFraction.sub_nonneg_direct rateAtMostOne) count
      have pointwise : ∀ atom, atom ∈ (transition item).atoms →
          Distribution.indicator (complementEvent event) atom.item *
              markovAvoidanceProbability transition event count atom.item ≤
            Distribution.indicator (complementEvent event) atom.item *
              (1 - rate) ^ count := by
        intro atom member
        have indicatorNonnegative :
            0 ≤ Distribution.indicator (complementEvent event) atom.item := by
          cases selected : complementEvent event atom.item <;>
            simp only [Distribution.indicator, selected] <;> decide
        exact
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (markovAvoidanceProbability_le_pow transition event rate
              rateNonnegative rateAtMostOne hitLower count atom.item)
            indicatorNonnegative
      have averaged := (transition item).expectation_mono
        (fun next => Distribution.indicator (complementEvent event) next *
          markovAvoidanceProbability transition event count next)
        (fun next => Distribution.indicator (complementEvent event) next *
          (1 - rate) ^ count)
        pointwise
      have complementBound :
          (transition item).probability (complementEvent event) ≤ 1 - rate := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          (hitLower item)
          ((transition item).probability (complementEvent event) - rate)
        calc
          (transition item).probability (complementEvent event) =
              rate +
                ((transition item).probability (complementEvent event) -
                  rate) := by ring1
          _ ≤ (transition item).probability event +
                ((transition item).probability (complementEvent event) -
                  rate) := shifted
          _ = ((transition item).probability event +
                (transition item).probability (complementEvent event)) -
                rate := by ring1
          _ = 1 - rate := by
            rw [(transition item).probability_add_complement event]
      calc
        markovAvoidanceProbability transition event (count + 1) item =
            (transition item).expectation (fun next =>
              Distribution.indicator (complementEvent event) next *
                markovAvoidanceProbability transition event count next) := rfl
        _ ≤ (transition item).expectation (fun next =>
              Distribution.indicator (complementEvent event) next *
                (1 - rate) ^ count) := averaged
        _ = (1 - rate) ^ count *
              (transition item).probability (complementEvent event) := by
          calc
            (transition item).expectation (fun next =>
                Distribution.indicator (complementEvent event) next *
                  (1 - rate) ^ count) =
                (transition item).expectation (fun next =>
                  (1 - rate) ^ count *
                    Distribution.indicator (complementEvent event) next) :=
              (transition item).expectation_congr _ _ (fun next => by ring1)
            _ = (1 - rate) ^ count *
                  (transition item).probability (complementEvent event) := by
              rw [(transition item).expectation_scale,
                (transition item).expectation_indicator]
        _ ≤ (1 - rate) ^ count * (1 - rate) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            complementBound allowanceNonnegative
        _ = (1 - rate) ^ (count + 1) := by
          rw [pow_succ]

/-- Uniform one-step hitting gives geometric avoidance decay for every finite
initial law. -/
theorem markovPaths_probability_pathAvoids_le_pow {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rate : Coordinate) (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (hitLower : ∀ item, rate ≤ (transition item).probability event)
    (count : Nat) (source : Distribution alpha) :
    (markovPaths transition count source).probability (pathAvoids event) ≤
      (1 - rate) ^ count := by
  rw [markovPaths_probability_pathAvoids]
  calc
    source.expectation
          (markovAvoidanceProbability transition event count) ≤
        source.expectation (fun _ => (1 - rate) ^ count) := by
      apply source.expectation_mono
      intro atom member
      exact markovAvoidanceProbability_le_pow transition event rate
        rateNonnegative rateAtMostOne hitLower count atom.item
    _ = (1 - rate) ^ count := source.expectation_constant _

/-- Uniform one-step hitting gives an explicit lower probability of at least
one visit in every supplied finite horizon. -/
theorem markovPaths_probability_pathHits_lower {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rate : Coordinate) (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (hitLower : ∀ item, rate ≤ (transition item).probability event)
    (count : Nat) (source : Distribution alpha) :
    1 - (1 - rate) ^ count ≤
      (markovPaths transition count source).probability (pathHits event) := by
  let paths := markovPaths transition count source
  have avoidanceBound :=
    markovPaths_probability_pathAvoids_le_pow transition event rate
      rateNonnegative rateAtMostOne hitLower count source
  have total := paths.probability_add_complement (pathAvoids event)
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    avoidanceBound
    (paths.probability (pathHits event) - (1 - rate) ^ count)
  calc
    1 - (1 - rate) ^ count =
        (paths.probability (pathAvoids event) +
            paths.probability (pathHits event)) -
          (1 - rate) ^ count := by
      rw [show paths.probability (pathHits event) =
          paths.probability (complementEvent (pathAvoids event)) by rfl,
        total]
    _ = paths.probability (pathAvoids event) +
        (paths.probability (pathHits event) - (1 - rate) ^ count) := by
      ring1
    _ ≤ (1 - rate) ^ count +
        (paths.probability (pathHits event) - (1 - rate) ^ count) := shifted
    _ = paths.probability (pathHits event) := by ring1

/-- Transition kernel obtained by executing exactly one displayed block of
the original transition. -/
def blockTransition {alpha : Type}
    (transition : alpha → Distribution alpha) (blockLength : Nat)
    (item : alpha) : Distribution alpha :=
  Distribution.iterate transition blockLength (Distribution.pure item)

/-- Explicit finite certificate that every state has a uniform positive
chance to hit an event at the end of one nonempty transition block. -/
structure UniformBlockHitCertificate {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool) where
  blockLength : Nat
  blockLengthPositive : 0 < blockLength
  rate : Coordinate
  ratePositive : 0 < rate
  rateAtMostOne : rate ≤ 1
  endpointHitLower : ∀ item,
    rate ≤ (blockTransition transition blockLength item).probability event

namespace UniformBlockHitCertificate

/-- After any supplied burn-in, a uniform block-hit certificate gives
geometric decay of the probability of avoiding the event at all subsequent
displayed block endpoints. -/
theorem avoidanceProbability_le_pow {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    (certificate : UniformBlockHitCertificate transition event)
    (source : Distribution alpha) (burnIn blockCount : Nat) :
    (markovPaths
        (blockTransition transition certificate.blockLength)
        blockCount (Distribution.iterate transition burnIn source)).probability
          (pathAvoids event) ≤
      (1 - certificate.rate) ^ blockCount := by
  exact markovPaths_probability_pathAvoids_le_pow
    (blockTransition transition certificate.blockLength) event
    certificate.rate certificate.ratePositive.le certificate.rateAtMostOne
    certificate.endpointHitLower blockCount
    (Distribution.iterate transition burnIn source)

/-- After any supplied burn-in, a uniform block-hit certificate gives an
explicit lower probability for a hit at one of the next displayed block
endpoints.  This is the finite quantitative recurrence statement intended
for later RFAP transversal use. -/
theorem hitProbability_lower {alpha : Type}
    {transition : alpha → Distribution alpha} {event : alpha → Bool}
    (certificate : UniformBlockHitCertificate transition event)
    (source : Distribution alpha) (burnIn blockCount : Nat) :
    1 - (1 - certificate.rate) ^ blockCount ≤
      (markovPaths
        (blockTransition transition certificate.blockLength)
        blockCount (Distribution.iterate transition burnIn source)).probability
          (pathHits event) := by
  exact markovPaths_probability_pathHits_lower
    (blockTransition transition certificate.blockLength) event
    certificate.rate certificate.ratePositive.le certificate.rateAtMostOne
    certificate.endpointHitLower blockCount
    (Distribution.iterate transition burnIn source)

end UniformBlockHitCertificate

end Distribution

end FiniteMeasure
