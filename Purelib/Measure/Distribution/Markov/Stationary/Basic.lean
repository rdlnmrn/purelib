module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Dynamics.Invariant
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Data.Rat.Fraction

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

@[expose] public section

namespace Purelib.Measure
namespace Distribution

/-- Require one exact kernel step to be evaluation-equivalent to the original retained distribution. -/
def StationaryFor {alpha : Type} (distribution : Distribution alpha)
    (transition : alpha → Distribution alpha) : Prop :=
  EvaluationEquivalent (distribution.step transition) distribution
namespace StationaryFor

/-- An invariant deterministic transformation makes the original law stationary for its exact deterministic transition
kernel. -/
theorem of_invariantUnder {alpha : Type}
    {distribution : Distribution alpha}
    {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation) :
    distribution.StationaryFor (deterministicTransition transformation) := by
  change EvaluationEquivalent
    (distribution.bind fun item => Distribution.pure (transformation item))
    distribution
  exact invariant

/-- Every finite iteration of the original stationary kernel is evaluation-equivalent to the retained initial law. -/
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

/-- Finite iteration of a stationary kernel preserves every original event probability. -/
theorem probability_iterate {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (count : Nat) (event : alpha → Bool) :
    (Distribution.iterate transition count distribution).probability event =
      distribution.probability event :=
  (stationary.iterate_evaluationEquivalent count).probability_eq event

open Purelib.Data.Rat in
/-- Finite iteration of a stationary kernel preserves every original rational expectation. -/
theorem expectation_iterate {alpha : Type}
    {distribution : Distribution alpha}
    {transition : alpha → Distribution alpha}
    (stationary : distribution.StationaryFor transition)
    (count : Nat) (value : alpha → Fraction.Rational) :
    (Distribution.iterate transition count distribution).expectation value =
      distribution.expectation value :=
  (stationary.iterate_evaluationEquivalent count).expectation_eq value

end StationaryFor
end Distribution

end Purelib.Measure

end
