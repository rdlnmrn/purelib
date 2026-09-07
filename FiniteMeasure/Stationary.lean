import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.MarkovReturn
import FiniteMeasure.Sampling

/-!
# Stationary finite dynamics and occupation averages

A finite transition preserves a displayed rational law when one exact step is
evaluation-equivalent to the original law.  This module proves preservation
at every supplied finite horizon and computes the exact expectation of a
finite Markov-path occupation count and frequency.  A final Chebyshev theorem
isolates the remaining dynamical input as the exact variance of that finite
occupation frequency.

This is a finite quantitative mean-ergodic interface, not an asymptotic
ergodic theorem: every path, horizon, event, expectation, and variance is
displayed finite rational data.
-/

namespace FiniteMeasure

/-- Number of entries of a displayed path that belong to an executable
event. -/
def pathVisitCount {alpha : Type} (event : alpha → Bool) :
    List alpha → Nat
  | [] => 0
  | item :: remaining =>
      (if event item then 1 else 0) + pathVisitCount event remaining

/-- Casting a path visit count exposes the head indicator and the remaining
count. -/
theorem cast_pathVisitCount_cons {alpha : Type} (event : alpha → Bool)
    (item : alpha) (remaining : List alpha) :
    (pathVisitCount event (item :: remaining) : Coordinate) =
      Distribution.indicator event item +
        (pathVisitCount event remaining : Coordinate) := by
  cases selected : event item
  · simp only [pathVisitCount, selected, Bool.false_eq_true,
      ↓reduceIte, Distribution.indicator, zero_add]
  · simp only [pathVisitCount, selected, ↓reduceIte,
      Distribution.indicator, Nat.cast_add, Nat.cast_one]

/-- Rational visit frequency in a path whose intended length is the supplied
positive natural number. -/
def pathVisitFrequency {alpha : Type} (count : Nat)
    (event : alpha → Bool) (path : List alpha) : Coordinate :=
  (count : Coordinate)⁻¹ * (pathVisitCount event path : Coordinate)

/-- A displayed path that avoids an event has zero visits. -/
theorem pathVisitCount_eq_zero_of_pathAvoids {alpha : Type}
    (event : alpha → Bool) : ∀ path : List alpha,
    pathAvoids event path = true → pathVisitCount event path = 0
  | [], selected => rfl
  | item :: remaining, selected => by
      cases head : event item
      · simp only [pathAvoids, head, Bool.not_false, Bool.true_and] at selected
        simp only [pathVisitCount, head, Bool.false_eq_true, ↓reduceIte,
          Nat.zero_add]
        exact pathVisitCount_eq_zero_of_pathAvoids event remaining selected
      · simp only [pathAvoids, head, Bool.not_true, Bool.false_and] at selected
        cases selected

namespace Distribution

namespace EvaluationEquivalent

/-- Evaluation-equivalent initial laws remain equivalent after one common
finite transition step. -/
theorem step {alpha : Type} {left right : Distribution alpha}
    (equivalent : EvaluationEquivalent left right)
    (transition : alpha → Distribution alpha) :
    EvaluationEquivalent (left.step transition) (right.step transition) :=
  equivalent.bind fun item => EvaluationEquivalent.refl (transition item)

/-- Evaluation-equivalent initial laws remain equivalent after every supplied
finite number of common transition steps. -/
theorem iterate {alpha : Type} {left right : Distribution alpha}
    (equivalent : EvaluationEquivalent left right)
    (transition : alpha → Distribution alpha) : ∀ count : Nat,
    EvaluationEquivalent (Distribution.iterate transition count left)
      (Distribution.iterate transition count right)
  | 0 => equivalent
  | count + 1 =>
      (equivalent.step transition).iterate transition count

end EvaluationEquivalent

/-- Exact stationarity of a displayed finite rational law for a finite
transition kernel. -/
def StationaryFor {alpha : Type} (distribution : Distribution alpha)
    (transition : alpha → Distribution alpha) : Prop :=
  EvaluationEquivalent (distribution.step transition) distribution

/-- Deterministic transition kernel associated with one executable self-map. -/
def deterministicTransition {alpha : Type} (transformation : alpha → alpha)
    (item : alpha) : Distribution alpha :=
  Distribution.pure (transformation item)

namespace StationaryFor

/-- An invariant deterministic law is stationary for its deterministic
transition kernel. -/
theorem of_invariantUnder {alpha : Type}
    {distribution : Distribution alpha}
    {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation) :
    distribution.StationaryFor (deterministicTransition transformation) := by
  change EvaluationEquivalent
    (distribution.bind fun item => Distribution.pure (transformation item))
    distribution
  exact invariant

/-- A stationary law is evaluation-equivalent to its law at every supplied
finite horizon. -/
theorem iterate_evaluationEquivalent {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition) : ∀ count : Nat,
    EvaluationEquivalent (Distribution.iterate transition count distribution)
      distribution
  | 0 => EvaluationEquivalent.refl distribution
  | count + 1 =>
      (stationary.iterate transition count).trans
        (stationary.iterate_evaluationEquivalent count)

/-- Stationarity preserves every executable event probability at every
supplied finite horizon. -/
theorem probability_iterate {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (count : Nat) (event : alpha → Bool) :
    (Distribution.iterate transition count distribution).probability event =
      distribution.probability event :=
  (stationary.iterate_evaluationEquivalent count).probability_eq event

/-- Stationarity preserves every rational expectation at every supplied
finite horizon. -/
theorem expectation_iterate {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (count : Nat) (value : alpha → Coordinate) :
    (Distribution.iterate transition count distribution).expectation value =
      distribution.expectation value :=
  (stationary.iterate_evaluationEquivalent count).expectation_eq value

end StationaryFor

/-- One statewise Markov-path step splits its expected visit count into the
next-state indicator and the remaining path expectation. -/
theorem markovPathFrom_expectation_pathVisitCount_succ {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (count : Nat) (item : alpha) :
    (markovPathFrom transition (count + 1) item).expectation
        (fun path => (pathVisitCount event path : Coordinate)) =
      (transition item).expectation (fun next =>
        Distribution.indicator event next +
          (markovPathFrom transition count next).expectation
            (fun path => (pathVisitCount event path : Coordinate))) := by
  rw [markovPathFrom, bind_expectation]
  exact (transition item).expectation_congr _ _ (fun next => by
    rw [(markovPathFrom transition count next).map_expectation]
    calc
      (markovPathFrom transition count next).expectation (fun remaining =>
          (pathVisitCount event (next :: remaining) : Coordinate)) =
          (markovPathFrom transition count next).expectation (fun remaining =>
            Distribution.indicator event next +
              (pathVisitCount event remaining : Coordinate)) :=
        (markovPathFrom transition count next).expectation_congr _ _
          (fun remaining => cast_pathVisitCount_cons event next remaining)
      _ = Distribution.indicator event next +
            (markovPathFrom transition count next).expectation (fun path =>
              (pathVisitCount event path : Coordinate)) := by
        rw [(markovPathFrom transition count next).expectation_add,
          (markovPathFrom transition count next).expectation_constant])

/-- Under a stationary finite law, the expected number of visits in a
displayed Markov path is exactly path length times event probability. -/
theorem StationaryFor.expectation_pathVisitCount {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (count : Nat) :
    (markovPaths transition count distribution).expectation
        (fun path => (pathVisitCount event path : Coordinate)) =
      (count : Coordinate) * distribution.probability event := by
  induction count with
  | zero =>
      rw [markovPaths, bind_expectation]
      calc
        distribution.expectation (fun item =>
              (markovPathFrom transition 0 item).expectation
                (fun path => (pathVisitCount event path : Coordinate))) =
            distribution.expectation (fun _ => (0 : Coordinate)) :=
          distribution.expectation_congr _ _ (fun item => by
            change (Distribution.pure ([] : List alpha)).expectation
                (fun path => (pathVisitCount event path : Coordinate)) = 0
            rw [pure_expectation]
            rfl)
        _ = 0 := distribution.expectation_constant 0
        _ = ((0 : Nat) : Coordinate) * distribution.probability event := by
          rw [Nat.cast_zero, zero_mul]
  | succ count inductionHypothesis =>
      rw [markovPaths, bind_expectation]
      have stepwise : distribution.expectation (fun item =>
            (markovPathFrom transition (count + 1) item).expectation
              (fun path => (pathVisitCount event path : Coordinate))) =
          distribution.expectation (fun item =>
            (transition item).expectation (fun next =>
              Distribution.indicator event next +
                (markovPathFrom transition count next).expectation
                  (fun path =>
                    (pathVisitCount event path : Coordinate)))) :=
        distribution.expectation_congr _ _ (fun item =>
          markovPathFrom_expectation_pathVisitCount_succ
            transition event count item)
      rw [stepwise, ← distribution.step_expectation]
      change (distribution.step transition).expectation (fun next =>
          Distribution.indicator event next +
            (markovPathFrom transition count next).expectation
              (fun path => (pathVisitCount event path : Coordinate))) =
        ((count + 1 : Nat) : Coordinate) * distribution.probability event
      rw [stationary.expectation_eq,
        distribution.expectation_add,
        distribution.expectation_indicator,
        show distribution.expectation (fun next =>
            (markovPathFrom transition count next).expectation
              (fun path => (pathVisitCount event path : Coordinate))) =
            (markovPaths transition count distribution).expectation
              (fun path => (pathVisitCount event path : Coordinate)) by
          rw [markovPaths, bind_expectation],
        inductionHypothesis,
        Nat.cast_add, Nat.cast_one]
      ring1

/-- Under a stationary finite law, expected path visit frequency is exactly
the event probability. -/
theorem StationaryFor.expectation_pathVisitFrequency {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (count : Nat)
    (countPositive : 0 < (count : Coordinate)) :
    (markovPaths transition count distribution).expectation
        (pathVisitFrequency count event) =
      distribution.probability event := by
  unfold pathVisitFrequency
  rw [(markovPaths transition count distribution).expectation_scale,
    stationary.expectation_pathVisitCount event count]
  exact positiveSampleCount_inv_mul_value count countPositive
    (distribution.probability event)

/-- Executable squared-deviation event for a stationary finite Markov
occupation frequency. -/
def stationaryPathVisitFrequencyDeviation {alpha : Type}
    (distribution : Distribution alpha) (count : Nat)
    (event : alpha → Bool) (threshold : Coordinate) :
    List alpha → Bool :=
  fun path => decide
    (threshold ^ 2 ≤
      (pathVisitFrequency count event path -
        distribution.probability event) ^ 2)

/-- Finite stationary occupation-frequency Chebyshev estimate.  A future
mixing or correlation proof need only bound the exact displayed variance on
the right; no limiting random process is required. -/
theorem StationaryFor.pathVisitFrequency_chebyshev {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (count : Nat)
    (countPositive : 0 < (count : Coordinate))
    (threshold : Coordinate) (thresholdPositive : 0 < threshold) :
    (markovPaths transition count distribution).probability
        (stationaryPathVisitFrequencyDeviation distribution count event
          threshold) ≤
      (markovPaths transition count distribution).variance
          (pathVisitFrequency count event) /
        threshold ^ 2 := by
  apply (markovPaths transition count distribution).chebyshev_bound
    (stationaryPathVisitFrequencyDeviation distribution count event threshold)
    (pathVisitFrequency count event) threshold thresholdPositive
  intro atom member selected
  rw [stationary.expectation_pathVisitFrequency event count countPositive]
  exact of_decide_eq_true selected

/-- Under a stationary law, the probability of avoiding a positive-mass
event is bounded by the exact variance of its displayed finite occupation
frequency.  A decorrelation calculation can therefore be supplied entirely
as a finite rational variance certificate. -/
theorem StationaryFor.pathAvoidance_probability_le_variance_div {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (eventPositive : 0 < distribution.probability event)
    (count : Nat) (countPositive : 0 < (count : Coordinate)) :
    (markovPaths transition count distribution).probability
        (pathAvoids event) ≤
      (markovPaths transition count distribution).variance
          (pathVisitFrequency count event) /
        distribution.probability event ^ 2 := by
  let paths := markovPaths transition count distribution
  have subset :
      paths.probability (pathAvoids event) ≤
        paths.probability
          (stationaryPathVisitFrequencyDeviation distribution count event
            (distribution.probability event)) := by
    unfold Distribution.probability
    apply eventWeight_mono
    intro atom member avoids
    have noVisits := pathVisitCount_eq_zero_of_pathAvoids event atom.item avoids
    unfold stationaryPathVisitFrequencyDeviation pathVisitFrequency
    apply decide_eq_true_eq.mpr
    rw [noVisits, Nat.cast_zero, mul_zero]
    have squareIdentity :
        ((0 : Coordinate) - distribution.probability event) ^ 2 =
          distribution.probability event ^ 2 := by ring1
    rw [squareIdentity]
    change distribution.probability event ^ 2 ≤
      distribution.probability event ^ 2
    exact le_rfl
  exact subset.trans
    (stationary.pathVisitFrequency_chebyshev event count countPositive
      (distribution.probability event) eventPositive)

/-- Variance-controlled finite recurrence: under a stationary law, a
positive-mass event is hit within the supplied path horizon with probability
at least one minus the exact occupation-frequency variance divided by the
squared event mass. -/
theorem StationaryFor.pathHit_probability_lower_of_variance {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (eventPositive : 0 < distribution.probability event)
    (count : Nat) (countPositive : 0 < (count : Coordinate)) :
    1 - (markovPaths transition count distribution).variance
          (pathVisitFrequency count event) /
          distribution.probability event ^ 2 ≤
      (markovPaths transition count distribution).probability
        (pathHits event) := by
  let paths := markovPaths transition count distribution
  let varianceRatio := paths.variance (pathVisitFrequency count event) /
    distribution.probability event ^ 2
  have avoidanceBound :=
    stationary.pathAvoidance_probability_le_variance_div event eventPositive
      count countPositive
  have total := paths.probability_add_complement (pathAvoids event)
  have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
    avoidanceBound (paths.probability (pathHits event) - varianceRatio)
  change 1 - varianceRatio ≤ paths.probability (pathHits event)
  calc
    1 - varianceRatio =
        (paths.probability (pathAvoids event) +
            paths.probability (pathHits event)) - varianceRatio := by
      rw [show paths.probability (pathHits event) =
          paths.probability (complementEvent (pathAvoids event)) by rfl,
        total]
    _ = paths.probability (pathAvoids event) +
        (paths.probability (pathHits event) - varianceRatio) := by ring1
    _ ≤ varianceRatio +
        (paths.probability (pathHits event) - varianceRatio) := shifted
    _ = paths.probability (pathHits event) := by ring1

end Distribution

end FiniteMeasure
