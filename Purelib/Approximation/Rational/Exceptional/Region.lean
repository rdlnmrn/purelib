module
public import Purelib.Integration.Partition.Exceptional.Region
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Effective rational variation outside finite regions

For every positive length request, the source computes a finite list of
closed rational regions of bounded total length. Its positive local variation
radius applies to ordered rational points whose connecting interval avoids
those same retained regions. No completed breakpoint or integral is supplied.
-/

public section

namespace Purelib.Approximation.Rational.Exceptional.Region

open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- A bounded source with computable small exceptional regions and variation away from them.

Every positive length request selects finite closed unit regions whose summed
length is within that request. Every positive variation request then selects a
positive radius controlling source readings between rational points whose
closed connecting interval meets none of those same regions. -/
structure Modulus (source : Fraction.Rational → Fraction.Rational) where
  /-- The nonnegative uniform source magnitude. -/ magnitude : Fraction.Rational
  /-- The global magnitude includes zero. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- Every rational source reading in the unit interval lies within the magnitude. -/ bounded :
    ∀ point, 0 ≤ point → point ≤ 1 → -magnitude ≤ source point ∧ source point ≤ magnitude
  /-- Compute finitely many closed exceptional regions for a positive length request. -/ regions :
    Fraction.Rational → List Interval
  /-- Every selected region has ordered endpoints within the unit interval. -/ region_bounds :
    ∀ length, 0 < length → ∀ region ∈ regions length,
      0 ≤ region.start ∧ region.start ≤ region.finish ∧ region.finish ≤ 1
  /-- The original selected region lengths sum to at most the requested length. -/ regions_length_le :
    ∀ length, 0 < length → ((regions length).map Interval.signedLength).sum ≤ length
  /-- Compute the positive radius from the region-length and variation requests. -/ radius :
    Fraction.Rational → Fraction.Rational → Fraction.Rational
  /-- Positive requests produce a positive local variation radius. -/ radius_pos :
    ∀ length, 0 < length → ∀ variation, 0 < variation → 0 < radius length variation
  /-- The source varies by at most the requested amount on a short region-free rational interval. -/ variation :
    ∀ length, 0 < length → ∀ variation, 0 < variation → ∀ first second,
      0 ≤ first → first ≤ second → second ≤ 1 →
      (∀ region ∈ regions length, ¬ (first ≤ region.finish ∧ region.start ≤ second)) →
      second - first < radius length variation →
        source first - variation ≤ source second ∧ source second ≤ source first + variation

constructive_injectivity Modulus

end Purelib.Approximation.Rational.Exceptional.Region

end
