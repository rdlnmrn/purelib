import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.DistributionEquivalence
import FiniteMeasure.OccurrenceSecondMoment

/-!
# Finite measure-preserving dynamics

This module packages the part of elementary dynamical measure theory that is
already meaningful for an explicitly displayed finite rational law.  A map
preserves a distribution when its finite pushforward has exactly the same
Boolean-event probabilities and rational expectations.  Orbit windows,
visit counts, and their second-moment hitting estimate are all indexed by
supplied natural numbers; no infinite orbit, limiting average, recurrence
principle, or completed measurable space is introduced.
-/

namespace FiniteMeasure

/-- Apply an executable self-map exactly the supplied number of times. -/
def iterateMap {alpha : Type} (transformation : alpha → alpha) :
    Nat → alpha → alpha
  | 0, item => item
  | count + 1, item => iterateMap transformation count (transformation item)

@[simp] theorem iterateMap_zero {alpha : Type}
    (transformation : alpha → alpha) (item : alpha) :
    iterateMap transformation 0 item = item := rfl

@[simp] theorem iterateMap_succ {alpha : Type}
    (transformation : alpha → alpha) (count : Nat) (item : alpha) :
    iterateMap transformation (count + 1) item =
      iterateMap transformation count (transformation item) := rfl

/-- Pull an executable event back from one displayed orbit time. -/
def orbitEvent {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (time : Nat) : alpha → Bool :=
  fun item => event (iterateMap transformation time item)

/-- The events observed in the half-open finite time window
`[start, start + count)`. -/
def orbitEvents {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (start : Nat) :
    Nat → List (alpha → Bool)
  | 0 => []
  | count + 1 =>
      orbitEvents transformation event start count ++
        [orbitEvent transformation event (start + count)]

@[simp] theorem orbitEvents_zero {alpha : Type}
    (transformation : alpha → alpha) (event : alpha → Bool)
    (start : Nat) :
    orbitEvents transformation event start 0 = [] := rfl

theorem orbitEvents_succ {alpha : Type}
    (transformation : alpha → alpha) (event : alpha → Bool)
    (start count : Nat) :
    orbitEvents transformation event start (count + 1) =
      orbitEvents transformation event start count ++
        [orbitEvent transformation event (start + count)] := rfl

/-- A finite orbit window contains exactly the requested number of events. -/
theorem orbitEvents_length {alpha : Type}
    (transformation : alpha → alpha) (event : alpha → Bool)
    (start : Nat) : ∀ count : Nat,
    (orbitEvents transformation event start count).length = count
  | 0 => rfl
  | count + 1 => by
      rw [orbitEvents_succ, List.length_append,
        orbitEvents_length transformation event start count]
      simp only [List.length_cons, List.length_nil]

/-- Executable event that at least one visit occurs in a displayed orbit
window. -/
def orbitHitEvent {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (start count : Nat) : alpha → Bool :=
  unionEvents (orbitEvents transformation event start count)

/-- Number of visits in a displayed orbit window. -/
def orbitVisitCount {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (start count : Nat) : alpha → Nat :=
  occurrenceCount (orbitEvents transformation event start count)

namespace Distribution

/-- Exact invariance of a finite rational distribution under an executable
self-map.  Atom-table ordering and duplicate rows are intentionally ignored;
all executable events and rational observables must agree. -/
def InvariantUnder {alpha : Type} (distribution : Distribution alpha)
    (transformation : alpha → alpha) : Prop :=
  EvaluationEquivalent (distribution.map transformation) distribution

namespace InvariantUnder

/-- Invariance preserves the probability of every executable preimage. -/
theorem probability_preimage {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) :
    distribution.probability (fun item => event (transformation item)) =
      distribution.probability event := by
  have preserved := invariant.probability_eq event
  rw [distribution.map_probability] at preserved
  exact preserved

/-- Invariance preserves the expectation of every rational observable. -/
theorem expectation_comp {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (value : alpha → Coordinate) :
    distribution.expectation (fun item => value (transformation item)) =
      distribution.expectation value := by
  have preserved := invariant.expectation_eq value
  rw [distribution.map_expectation] at preserved
  exact preserved

/-- Every supplied finite iterate preserves executable event probability. -/
theorem probability_iterate {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) : ∀ time : Nat,
    distribution.probability (orbitEvent transformation event time) =
      distribution.probability event
  | 0 => rfl
  | time + 1 => by
      calc
        distribution.probability
              (orbitEvent transformation event (time + 1)) =
            distribution.probability (fun item =>
              orbitEvent transformation event time
                (transformation item)) := rfl
        _ = distribution.probability
              (orbitEvent transformation event time) :=
          invariant.probability_preimage _
        _ = distribution.probability event :=
          invariant.probability_iterate event time

/-- Every supplied finite iterate preserves rational expectation. -/
theorem expectation_iterate {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (value : alpha → Coordinate) : ∀ time : Nat,
    distribution.expectation (fun item =>
        value (iterateMap transformation time item)) =
      distribution.expectation value
  | 0 => rfl
  | time + 1 => by
      calc
        distribution.expectation (fun item =>
              value (iterateMap transformation (time + 1) item)) =
            distribution.expectation (fun item =>
              value (iterateMap transformation time
                (transformation item))) := rfl
        _ = distribution.expectation (fun item =>
              value (iterateMap transformation time item)) :=
          invariant.expectation_comp
            (fun item => value (iterateMap transformation time item))
        _ = distribution.expectation value :=
          invariant.expectation_iterate value time

/-- A displayed finite iterate is itself measure preserving. -/
theorem iterate {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (time : Nat) :
    distribution.InvariantUnder (iterateMap transformation time) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [distribution.map_expectation]
  exact invariant.expectation_iterate value time

/-- Exact total event mass in any delayed orbit window of an invariant
finite law. -/
theorem orbitEvents_probability_sum {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) (start : Nat) : ∀ count : Nat,
    ((orbitEvents transformation event start count).map
        distribution.probability).sum =
      (count : Coordinate) * distribution.probability event
  | 0 => by
      simp only [orbitEvents_zero, List.map_nil, List.sum_nil,
        Nat.cast_zero, zero_mul]
  | count + 1 => by
      rw [orbitEvents_succ, List.map_append, List.sum_append,
        invariant.orbitEvents_probability_sum event start count]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [invariant.probability_iterate event (start + count), Nat.cast_add,
        Nat.cast_one]
      ring1

/-- Exact first moment of the visit count in any delayed finite orbit
window.  This is the finite time-average identity for an indicator. -/
theorem expectation_orbitVisitCount {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) (start count : Nat) :
    distribution.expectation (fun item =>
        (orbitVisitCount transformation event start count item :
          Coordinate)) =
      (count : Coordinate) * distribution.probability event := by
  unfold orbitVisitCount
  rw [distribution.expectation_occurrenceCount,
    invariant.orbitEvents_probability_sum]

/-- Finite second-moment lower bound for hitting an invariant positive-mass
event in a delayed orbit window.  The remaining denominator is an exact
finite correlation term, so a later dynamical argument can discharge it by
an explicit decorrelation or return certificate rather than an infinite
ergodic theorem. -/
theorem orbitHit_secondMoment_lower_bound {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) (start count : Nat)
    (countPositive : 0 < count)
    (eventPositive : 0 < distribution.probability event) :
    ((count : Coordinate) * distribution.probability event) ^ 2 /
        ((count : Coordinate) * distribution.probability event +
          2 * distribution.pairIntersectionProbabilitySum
            (orbitEvents transformation event start count)) ≤
      distribution.probability
        (orbitHitEvent transformation event start count) := by
  have castCountPositive : 0 < (count : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct countPositive
  have probabilitySumPositive :
      0 < ((orbitEvents transformation event start count).map
        distribution.probability).sum := by
    rw [invariant.orbitEvents_probability_sum]
    exact mul_pos castCountPositive eventPositive
  have lower := distribution.secondMoment_union_lower_bound
    (orbitEvents transformation event start count) probabilitySumPositive
  rw [invariant.orbitEvents_probability_sum] at lower
  exact lower

end InvariantUnder

end Distribution

end FiniteMeasure
