module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Dynamics.Invariant
import Purelib.Measure.Event.Family
import Purelib.Measure.Event.Orbit
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Occurrence.SecondMoment
import Purelib.Data.Rat.Fraction.Order.Basic
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
namespace InvariantUnder

open Purelib.Data.Rat in
/-- An invariant finite law gives a second-moment lower bound on hitting an event within the retained orbit window.

The event has positive probability and the window has positive length; the denominator retains all pair intersections in
that same finite window. -/
theorem orbitHit_secondMoment_lower_bound {alpha : Type}
    {distribution : Distribution alpha} {transformation : alpha → alpha}
    (invariant : distribution.InvariantUnder transformation)
    (event : alpha → Bool) (start count : Nat)
    (countPositive : 0 < count)
    (eventPositive : 0 < distribution.probability event) :
    ((count : Fraction.Rational) * distribution.probability event) ^ 2 /
        ((count : Fraction.Rational) * distribution.probability event +
          2 * distribution.pairIntersectionProbabilitySum
            (orbitEvents transformation event start count)) ≤
      distribution.probability
        (orbitHitEvent transformation event start count) := by
  have castCountPositive : 0 < (count : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct countPositive
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

end Purelib.Measure

end
