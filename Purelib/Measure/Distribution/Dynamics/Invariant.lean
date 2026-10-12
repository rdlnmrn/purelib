module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Function.Iterate
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Occurrence.FirstMoment
import Purelib.Measure.Event.Occurrence
public import Purelib.Measure.Event.Orbit
import Purelib.Data.Rat.Fraction.Arithmetic

section
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

@[expose] public section

namespace Purelib.Measure
namespace Distribution

/-- Require the exact pushforward by the supplied transformation to be evaluation-equivalent to the original
distribution. -/
def InvariantUnder {alpha : Type} (distribution : Distribution alpha)
    (transformation : alpha → alpha) : Prop :=
  EvaluationEquivalent (distribution.map transformation) distribution

namespace InvariantUnder

/-- An invariant distribution assigns an event and its transformation preimage the same probability. -/
theorem probability_preimage {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) :
    distribution.probability (fun item => event (transformation item)) =
      distribution.probability event := by
  have preserved := invariant.probability_eq event
  rw [distribution.map_probability] at preserved
  exact preserved

open Purelib.Data.Rat in
/-- Composing an observable with the invariant transformation preserves its original expectation. -/
theorem expectation_comp {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (value : alpha → Fraction.Rational) :
    distribution.expectation (fun item => value (transformation item)) =
      distribution.expectation value := by
  have preserved := invariant.expectation_eq value
  rw [distribution.map_expectation] at preserved
  exact preserved

/-- Every finite orbit-event preimage has the same probability under the exact invariant distribution. -/
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

open Purelib.Data in
open Purelib.Data.Rat in
/-- Composing an observable with any finite iterate of the invariant transformation preserves expectation. -/
theorem expectation_iterate {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (value : alpha → Fraction.Rational) : ∀ time : Nat,
    distribution.expectation (fun item =>
        value (Function.iterateMap transformation time item)) =
      distribution.expectation value
  | 0 => rfl
  | time + 1 => by
      calc
        distribution.expectation (fun item =>
              value (Function.iterateMap transformation (time + 1) item)) =
            distribution.expectation (fun item =>
              value (Function.iterateMap transformation time
                (transformation item))) := rfl
        _ = distribution.expectation (fun item =>
              value (Function.iterateMap transformation time item)) :=
          invariant.expectation_comp
            (fun item => value (Function.iterateMap transformation time item))
        _ = distribution.expectation value :=
          invariant.expectation_iterate value time

open Purelib.Data in
/-- Every finite iterate of the original transformation preserves the same retained distribution in evaluation. -/
theorem iterate {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (time : Nat) :
    distribution.InvariantUnder (Function.iterateMap transformation time) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [distribution.map_expectation]
  exact invariant.expectation_iterate value time

open Purelib.Data.Rat in
open Purelib.Data.List in
open Purelib.Algebra in
/-- The exact finite orbit-event window has probability sum equal to window length times the original event probability.
-/
theorem orbitEvents_probability_sum {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) (start : Nat) : ∀ count : Nat,
    ((orbitEvents transformation event start count).map
        distribution.probability).sum =
      (count : Fraction.Rational) * distribution.probability event
  | 0 => by
      simp only [orbitEvents_zero, List.map_nil, List.sum_nil,
        Nat.cast_zero, zero_mul, -eq_self, -iff_self]
      rfl
  | count + 1 => by
      rw [orbitEvents_succ, Map.map_append,
        Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc,
        invariant.orbitEvents_probability_sum event start count]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [invariant.probability_iterate event (start + count), NatCast.add,
        Nat.cast_one]
      ring1

open Purelib.Data.Rat in
/-- Expected visit count in the exact finite orbit window equals its length times the original event probability. -/
theorem expectation_orbitVisitCount {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) (start count : Nat) :
    distribution.expectation (fun item =>
        (orbitVisitCount transformation event start count item :
          Fraction.Rational)) =
      (count : Fraction.Rational) * distribution.probability event := by
  unfold orbitVisitCount
  rw [distribution.expectation_occurrenceCount,
    invariant.orbitEvents_probability_sum]
end InvariantUnder

end Distribution

end Purelib.Measure

end
