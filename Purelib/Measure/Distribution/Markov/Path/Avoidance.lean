module
import Purelib.Algebra.Group.Basic
public import Purelib.Measure.Distribution.Markov.Path.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

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

open Purelib.Data.Rat in
/-- Compute finite-step avoidance probability recursively from the exact transition kernel and event.

Zero steps contribute one; each successor multiplies the next state's complementary-event indicator by its retained
remaining-step avoidance probability before averaging. -/
@[expose] def markovAvoidanceProbability {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool) :
    Nat → alpha → Fraction.Rational
  | 0, _ => 1
  | count + 1, item =>
      (transition item).expectation fun next =>
        Distribution.indicator (complementEvent event) next *
          markovAvoidanceProbability transition event count next

namespace Distribution

section
open Purelib
/-- Avoidance probability for the exact path law from one state equals the recursive avoidance computation. -/
theorem markovPathFrom_probability_pathAvoids {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (count : Nat) (item : alpha) :
    (markovPathFrom transition count item).probability (Data.List.pathAvoids event) =
      markovAvoidanceProbability transition event count item := by
  induction count generalizing item with
  | zero =>
      change (Distribution.pure ([] : List alpha)).probability
          (Data.List.pathAvoids event) = 1
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
                  (fun remaining => Data.List.pathAvoids event (next :: remaining)) =
                (markovPathFrom transition count next).probability
                  (Data.List.pathAvoids event) :=
              (markovPathFrom transition count next).probability_congr _ _
                (fun remaining => by
                  simp only [Data.List.pathAvoids, selected, Bool.not_false,
                    Bool.true_and, -eq_self, -iff_self]
                  rfl)
            _ = markovAvoidanceProbability transition event count next :=
              inductionHypothesis next
            _ = Distribution.indicator (complementEvent event) next *
                  markovAvoidanceProbability transition event count next := by
              simp only [complementEvent, selected, Bool.not_false,
                Distribution.indicator, one_mul, -eq_self, -iff_self]
              rfl
        · calc
            (markovPathFrom transition count next).probability
                  (fun remaining => Data.List.pathAvoids event (next :: remaining)) =
                (markovPathFrom transition count next).probability
                  (fun _ => false) :=
              (markovPathFrom transition count next).probability_congr _ _
                (fun remaining => by
                  simp only [Data.List.pathAvoids, selected, Bool.not_true,
                    Bool.false_and, -eq_self, -iff_self]
                  rfl)
            _ = 0 :=
              (markovPathFrom transition count next).probability_false
            _ = Distribution.indicator (complementEvent event) next *
                  markovAvoidanceProbability transition event count next := by
              simp only [complementEvent, selected, Bool.not_true,
                Distribution.indicator, zero_mul, -eq_self, -iff_self]
              rfl)

/-- Avoidance probability for the exact original-source path law equals the source expectation of recursive avoidance
probabilities. -/
theorem markovPaths_probability_pathAvoids {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (count : Nat) (source : Distribution alpha) :
    (markovPaths transition count source).probability (Data.List.pathAvoids event) =
      source.expectation
        (markovAvoidanceProbability transition event count) := by
  rw [markovPaths, bind_probability]
  exact source.expectation_congr _ _ (fun item =>
    markovPathFrom_probability_pathAvoids transition event count item)

end

open Purelib.Data.Rat in
/-- A uniform one-step hit lower bound gives the geometric finite-step avoidance upper bound from every original state.
-/
theorem markovAvoidanceProbability_le_pow {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rate : Fraction.Rational) (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (hitLower : ∀ item, rate ≤ (transition item).probability event) :
    ∀ (count : Nat) (item : alpha),
      markovAvoidanceProbability transition event count item ≤
        (1 - rate) ^ count
  | 0, item => le_rfl
  | count + 1, item => by
      have allowanceNonnegative : 0 ≤ (1 - rate) ^ count :=
        Fraction.Order.Arithmetic.pow_nonneg_direct
          (Fraction.Order.Arithmetic.sub_nonneg_direct rateAtMostOne) count
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
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
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
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          (hitLower item)
          ((transition item).probability (complementEvent event) - rate)
        calc
          (transition item).probability (complementEvent event) =
              rate +
                ((transition item).probability (complementEvent event) -
                  rate) := by ring0
          _ ≤ (transition item).probability event +
                ((transition item).probability (complementEvent event) -
                  rate) := shifted
          _ = ((transition item).probability event +
                (transition item).probability (complementEvent event)) -
                rate := by ring0
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
              (transition item).expectation_congr _ _ (fun next => Fraction.Field.mul_comm _ _)
            _ = (1 - rate) ^ count *
                  (transition item).probability (complementEvent event) := by
              rw [(transition item).expectation_scale,
                (transition item).expectation_indicator]
        _ ≤ (1 - rate) ^ count * (1 - rate) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            complementBound allowanceNonnegative
        _ = (1 - rate) ^ (count + 1) := by
          rw [pow_succ]

open Purelib
open Purelib.Data.Rat
/-- The same uniform hit lower bound gives a geometric avoidance bound for paths from the exact original source law. -/
theorem markovPaths_probability_pathAvoids_le_pow {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rate : Fraction.Rational) (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (hitLower : ∀ item, rate ≤ (transition item).probability event)
    (count : Nat) (source : Distribution alpha) :
    (markovPaths transition count source).probability (Data.List.pathAvoids event) ≤
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

/-- A uniform one-step hit lower bound gives the complementary geometric lower bound for hitting within the exact finite
path. -/
theorem markovPaths_probability_pathHits_lower {alpha : Type}
    (transition : alpha → Distribution alpha) (event : alpha → Bool)
    (rate : Fraction.Rational) (rateNonnegative : 0 ≤ rate)
    (rateAtMostOne : rate ≤ 1)
    (hitLower : ∀ item, rate ≤ (transition item).probability event)
    (count : Nat) (source : Distribution alpha) :
    1 - (1 - rate) ^ count ≤
      (markovPaths transition count source).probability (Data.List.pathHits event) := by
  let paths := markovPaths transition count source
  have avoidanceBound :=
    markovPaths_probability_pathAvoids_le_pow transition event rate
      rateNonnegative rateAtMostOne hitLower count source
  have total := paths.probability_add_complement (Data.List.pathAvoids event)
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    avoidanceBound
    (paths.probability (Data.List.pathHits event) - (1 - rate) ^ count)
  calc
    1 - (1 - rate) ^ count =
        (paths.probability (Data.List.pathAvoids event) +
            paths.probability (Data.List.pathHits event)) -
          (1 - rate) ^ count := by
      rw [show paths.probability (Data.List.pathHits event) =
          paths.probability (complementEvent (Data.List.pathAvoids event)) by rfl,
        total]
    _ = paths.probability (Data.List.pathAvoids event) +
        (paths.probability (Data.List.pathHits event) - (1 - rate) ^ count) := by
      change (paths.probability (Data.List.pathAvoids event) +
        paths.probability (Data.List.pathHits event)) + -((1 - rate) ^ count) =
          paths.probability (Data.List.pathAvoids event) +
            (paths.probability (Data.List.pathHits event) + -((1 - rate) ^ count))
      exact Fraction.Field.add_assoc _ _ _
    _ ≤ (1 - rate) ^ count +
        (paths.probability (Data.List.pathHits event) - (1 - rate) ^ count) := shifted
    _ = paths.probability (Data.List.pathHits event) := by
      change (1 - rate) ^ count +
        (paths.probability (Data.List.pathHits event) + -((1 - rate) ^ count)) =
          paths.probability (Data.List.pathHits event)
      exact (Fraction.Field.add_assoc _ _ _).symm.trans
        (Algebra.Group.add_sub_cancel_left _ _)

end Distribution

end Purelib.Measure

end
