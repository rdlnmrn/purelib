module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Distribution.Markov.Stationary.Basic
public import Purelib.Measure.Distribution.Markov.Path.Basic
import Purelib.Data.Rat.NatCast.Reciprocal
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
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

public section

namespace Purelib.Measure
namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Expected visits in a successor path equal the transition expectation of the next indicator plus exact remaining-path
expected visits. -/
theorem markovPathFrom_expectation_pathVisitCount_succ {alpha : Type}
    (transition : alpha → Measure.Distribution alpha) (event : alpha → Bool)
    (count : Nat) (item : alpha) :
    (markovPathFrom transition (count + 1) item).expectation
        (fun path => (Data.List.pathVisitCount event path : Fraction.Rational)) =
      (transition item).expectation (fun next =>
        Distribution.indicator event next +
          (markovPathFrom transition count next).expectation
            (fun path => (Data.List.pathVisitCount event path : Fraction.Rational))) := by
  rw [markovPathFrom, bind_expectation]
  exact (transition item).expectation_congr _ _ (fun next => by
    rw [(markovPathFrom transition count next).map_expectation]
    calc
      (markovPathFrom transition count next).expectation (fun remaining =>
          (Data.List.pathVisitCount event (next :: remaining) : Fraction.Rational)) =
          (markovPathFrom transition count next).expectation (fun remaining =>
            Distribution.indicator event next +
              (Data.List.pathVisitCount event remaining : Fraction.Rational)) :=
        (markovPathFrom transition count next).expectation_congr _ _
          (fun remaining => cast_pathVisitCount_cons event next remaining)
      _ = Distribution.indicator event next +
            (markovPathFrom transition count next).expectation (fun path =>
              (Data.List.pathVisitCount event path : Fraction.Rational)) := by
        rw [(markovPathFrom transition count next).expectation_add,
          (markovPathFrom transition count next).expectation_constant])

open Purelib.Measure in
/-- Under the exact stationary starting law, expected path visits equal step count times original event probability. -/
theorem StationaryFor.expectation_pathVisitCount {alpha : Type}
    {distribution : Measure.Distribution alpha}
    {transition : alpha → Measure.Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (count : Nat) :
    (markovPaths transition count distribution).expectation
        (fun path => (Data.List.pathVisitCount event path : Fraction.Rational)) =
      (count : Fraction.Rational) * distribution.probability event := by
  induction count with
  | zero =>
      rw [markovPaths, bind_expectation]
      calc
        distribution.expectation (fun item =>
              (markovPathFrom transition 0 item).expectation
                (fun path => (Data.List.pathVisitCount event path : Fraction.Rational))) =
            distribution.expectation (fun _ => (0 : Fraction.Rational)) :=
          distribution.expectation_congr _ _ (fun item => by
            change (Distribution.pure ([] : List alpha)).expectation
                (fun path => (Data.List.pathVisitCount event path : Fraction.Rational)) = 0
            rw [pure_expectation]
            rfl)
        _ = 0 := distribution.expectation_constant 0
        _ = ((0 : Nat) : Fraction.Rational) * distribution.probability event := by
          rw [Nat.cast_zero, zero_mul]
  | succ count inductionHypothesis =>
      rw [markovPaths, bind_expectation]
      have stepwise : distribution.expectation (fun item =>
            (markovPathFrom transition (count + 1) item).expectation
              (fun path => (Data.List.pathVisitCount event path : Fraction.Rational))) =
          distribution.expectation (fun item =>
            (transition item).expectation (fun next =>
              Distribution.indicator event next +
                (markovPathFrom transition count next).expectation
                  (fun path =>
                    (Data.List.pathVisitCount event path : Fraction.Rational)))) :=
        distribution.expectation_congr _ _ (fun item =>
          Distribution.markovPathFrom_expectation_pathVisitCount_succ
            transition event count item)
      rw [stepwise, ← distribution.step_expectation]
      change (distribution.step transition).expectation (fun next =>
          Distribution.indicator event next +
            (markovPathFrom transition count next).expectation
              (fun path => (Data.List.pathVisitCount event path : Fraction.Rational))) =
        ((count + 1 : Nat) : Fraction.Rational) * distribution.probability event
      rw [stationary.expectation_eq,
        distribution.expectation_add,
        distribution.expectation_indicator,
        show distribution.expectation (fun next =>
            (markovPathFrom transition count next).expectation
              (fun path => (Data.List.pathVisitCount event path : Fraction.Rational))) =
            (markovPaths transition count distribution).expectation
              (fun path => (Data.List.pathVisitCount event path : Fraction.Rational)) by
          rw [markovPaths, bind_expectation],
        inductionHypothesis,
        Algebra.NatCast.add, Nat.cast_one]
      ring1

/-- At positive step count, expected stationary path visit frequency equals original event probability. -/
theorem StationaryFor.expectation_pathVisitFrequency {alpha : Type}
    {distribution : Measure.Distribution alpha}
    {transition : alpha → Measure.Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (count : Nat)
    (countPositive : 0 < (count : Fraction.Rational)) :
    (markovPaths transition count distribution).expectation
        (Measure.pathVisitFrequency count event) =
      distribution.probability event := by
  unfold Measure.pathVisitFrequency
  rw [(markovPaths transition count distribution).expectation_scale,
    stationary.expectation_pathVisitCount event count]
  exact positiveSampleCount_inv_mul_value count countPositive
    (distribution.probability event)

/-- Select paths whose frequency's squared deviation from the original event probability reaches threshold squared. -/
@[expose] def stationaryPathVisitFrequencyDeviation {alpha : Type}
    (distribution : Measure.Distribution alpha) (count : Nat)
    (event : alpha → Bool) (threshold : Fraction.Rational) :
    List alpha → Bool :=
  fun path => decide
    (threshold ^ 2 ≤
      (Measure.pathVisitFrequency count event path -
        distribution.probability event) ^ 2)

section
open Purelib.Measure
/-- At positive count and threshold, stationary visit-frequency deviation probability is bounded by its exact path-law
variance divided by threshold squared. -/
theorem StationaryFor.pathVisitFrequency_chebyshev {alpha : Type}
    {distribution : Measure.Distribution alpha}
    {transition : alpha → Measure.Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (count : Nat)
    (countPositive : 0 < (count : Fraction.Rational))
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold) :
    (markovPaths transition count distribution).probability
        (Distribution.stationaryPathVisitFrequencyDeviation distribution count event
          threshold) ≤
      (markovPaths transition count distribution).variance
          (Measure.pathVisitFrequency count event) /
        threshold ^ 2 := by
  apply (markovPaths transition count distribution).chebyshev_bound
    (Distribution.stationaryPathVisitFrequencyDeviation distribution count event threshold)
    (Measure.pathVisitFrequency count event) threshold thresholdPositive
  intro atom member selected
  rw [stationary.expectation_pathVisitFrequency event count countPositive]
  exact of_decide_eq_true selected

/-- For a positive-probability event, stationary finite-path avoidance is bounded by exact frequency variance divided by
original event probability squared. -/
theorem StationaryFor.pathAvoidance_probability_le_variance_div {alpha : Type}
    {distribution : Measure.Distribution alpha}
    {transition : alpha → Measure.Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (eventPositive : 0 < distribution.probability event)
    (count : Nat) (countPositive : 0 < (count : Fraction.Rational)) :
    (markovPaths transition count distribution).probability
        (Data.List.pathAvoids event) ≤
      (markovPaths transition count distribution).variance
          (Measure.pathVisitFrequency count event) /
        distribution.probability event ^ 2 := by
  let paths := markovPaths transition count distribution
  have subset :
      paths.probability (Data.List.pathAvoids event) ≤
        paths.probability
          (Distribution.stationaryPathVisitFrequencyDeviation distribution count event
            (distribution.probability event)) := by
    unfold Distribution.probability
    apply eventWeight_mono
    intro atom member avoids
    have noVisits := Data.List.pathVisitCount_eq_zero_of_pathAvoids event atom.item avoids
    unfold Distribution.stationaryPathVisitFrequencyDeviation Measure.pathVisitFrequency
    apply decide_eq_true
    rw [noVisits, Nat.cast_zero, mul_zero]
    have squareIdentity :
        ((0 : Fraction.Rational) - distribution.probability event) ^ 2 =
          distribution.probability event ^ 2 := by ring1
    rw [squareIdentity]
    change distribution.probability event ^ 2 ≤
      distribution.probability event ^ 2
    exact le_rfl
  exact subset.trans
    (stationary.pathVisitFrequency_chebyshev event count countPositive
      (distribution.probability event) eventPositive)

end

/-- Stationary finite-path hitting has the complementary lower bound determined by exact frequency variance and positive
original event probability. -/
theorem StationaryFor.pathHit_probability_lower_of_variance {alpha : Type}
    {distribution : Measure.Distribution alpha}
    {transition : alpha → Measure.Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (event : alpha → Bool) (eventPositive : 0 < distribution.probability event)
    (count : Nat) (countPositive : 0 < (count : Fraction.Rational)) :
    1 - (markovPaths transition count distribution).variance
          (Measure.pathVisitFrequency count event) /
          distribution.probability event ^ 2 ≤
      (markovPaths transition count distribution).probability
        (Data.List.pathHits event) := by
  let paths := markovPaths transition count distribution
  let varianceRatio := paths.variance (Measure.pathVisitFrequency count event) /
    distribution.probability event ^ 2
  have avoidanceBound :=
    stationary.pathAvoidance_probability_le_variance_div event eventPositive
      count countPositive
  have total := paths.probability_add_complement (Data.List.pathAvoids event)
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    avoidanceBound (paths.probability (Data.List.pathHits event) - varianceRatio)
  change 1 - varianceRatio ≤ paths.probability (Data.List.pathHits event)
  calc
    1 - varianceRatio =
        (paths.probability (Data.List.pathAvoids event) +
            paths.probability (Data.List.pathHits event)) - varianceRatio := by
      rw [show paths.probability (Data.List.pathHits event) =
          paths.probability (complementEvent (Data.List.pathAvoids event)) by rfl,
        total]
    _ = paths.probability (Data.List.pathAvoids event) +
        (paths.probability (Data.List.pathHits event) - varianceRatio) := by ring1
    _ ≤ varianceRatio +
        (paths.probability (Data.List.pathHits event) - varianceRatio) := shifted
    _ = paths.probability (Data.List.pathHits event) := by ring1

end

end Distribution

end Purelib.Measure

end
