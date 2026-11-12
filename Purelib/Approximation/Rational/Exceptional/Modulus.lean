module
public import Purelib.Approximation.Rational.Uniform.Modulus
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Effective rational variation away from finite exceptional points

An exact source carries a finite list of rational exceptional points, a
global rational magnitude bound and a computed variation radius away from
those points. The contract does not assume an integration result or a
successful partition.
-/

public section

namespace Purelib.Approximation.Rational.Exceptional

open Purelib.Data.Rat

set_option genInjectivity false in
/-- A bounded rational source with effective uniform variation away from finitely many rational points.

The source is globally enclosed by the supplied nonnegative magnitude on the
unit interval. The computed radius controls ordered rational points whenever
their closed connecting interval contains none of the retained exceptions. -/
structure Modulus (source : Fraction.Rational → Fraction.Rational) where
  /-- The finite ordered rational exceptional points. -/ points : List Fraction.Rational
  /-- The retained nonnegative global magnitude. -/ magnitude : Fraction.Rational
  /-- The global magnitude is nonnegative, including the zero case. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- Every rational source reading in the unit interval lies in the symmetric global range. -/ bounded :
    ∀ point, 0 ≤ point → point ≤ 1 → -magnitude ≤ source point ∧ source point ≤ magnitude
  /-- Compute a radius for the requested positive regular-piece variation. -/ radius :
    Fraction.Rational → Fraction.Rational
  /-- Positive variation requests yield positive rational radii. -/ radius_pos :
    ∀ variation, 0 < variation → 0 < radius variation
  /-- The radius controls ordered points whose connecting interval contains no retained exception. -/ variation :
    ∀ variation, 0 < variation → ∀ first second, 0 ≤ first → first ≤ second → second ≤ 1 →
      (∀ exceptional ∈ points, ¬ (first ≤ exceptional ∧ exceptional ≤ second)) →
      second - first < radius variation →
        source first - variation ≤ source second ∧ source second ≤ source first + variation

constructive_injectivity Modulus

/-- A globally bounded uniformly continuous source has an empty finite exceptional list. -/
@[expose] def ofUniform {source : Fraction.Rational → Fraction.Rational} (uniform : Rational.Uniform.Modulus source)
    (magnitude : Fraction.Rational) (nonnegative : 0 ≤ magnitude)
    (bounded : ∀ point, 0 ≤ point → point ≤ 1 → -magnitude ≤ source point ∧ source point ≤ magnitude) :
    Modulus source :=
  { points := []
    magnitude := magnitude
    magnitude_nonnegative := nonnegative
    bounded := bounded
    radius := uniform.radius
    radius_pos := uniform.radius_pos
    variation := fun variation positive first second lower ordered upper _ small =>
      uniform.variation variation positive first second lower ordered upper small }

end Purelib.Approximation.Rational.Exceptional

end
