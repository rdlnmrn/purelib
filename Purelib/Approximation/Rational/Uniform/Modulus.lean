module
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Effective rational uniform variation

A modulus computes a positive rational distance for each positive variation
request. Its law concerns the actual source values at rational points of the
unit interval; it does not assume an integral enclosure or a completed value.
-/

public section

namespace Purelib.Approximation.Rational.Uniform

open Purelib.Data.Rat

set_option genInjectivity false in
/-- An effective one-sided uniform variation modulus for an exact rational source.

Every positive requested variation computes a positive distance. Ordered
rational points in the unit interval within that distance have source values
within the requested variation in both directions. -/
structure Modulus (source : Fraction.Rational → Fraction.Rational) where
  /-- Compute the positive distance for the retained variation request. -/ radius :
    Fraction.Rational → Fraction.Rational
  /-- Positive variation requests produce a positive rational distance. -/ radius_pos :
    ∀ variation, 0 < variation → 0 < radius variation
  /-- The computed distance controls both directed source differences on the unit interval. -/ variation :
    ∀ variation, 0 < variation → ∀ first second, 0 ≤ first → first ≤ second → second ≤ 1 →
      second - first < radius variation →
        source first - variation ≤ source second ∧ source second ≤ source first + variation

constructive_injectivity Modulus

/-- Transport a uniform modulus along equality of the original rational unit-interval readings.

The radius and every variation request come from the same original modulus.
Equality is required only at rational points of the retained unit interval;
no equality of source functions or completed values is selected. -/
@[expose] def Modulus.transport {source target : Fraction.Rational → Fraction.Rational} (modulus : Modulus source)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → target point = source point) : Modulus target where
  radius := modulus.radius
  radius_pos := modulus.radius_pos
  variation := by
    intro variation positive first second firstLower ordered secondUpper small
    have firstUpper : first ≤ 1 := Fraction.Order.Basic.le_trans _ _ _ ordered secondUpper
    have secondLower : 0 ≤ second := Fraction.Order.Basic.le_trans _ _ _ firstLower ordered
    rw [same first firstLower firstUpper, same second secondLower secondUpper]
    exact modulus.variation variation positive first second firstLower ordered secondUpper small

end Purelib.Approximation.Rational.Uniform

end
