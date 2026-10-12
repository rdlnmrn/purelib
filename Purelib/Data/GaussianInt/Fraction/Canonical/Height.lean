module
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Fraction.Canonical

open Purelib.Data

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Fraction

open Purelib.Data.GaussianInt.Fraction.Canonical

section
@[expose] public section

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace Purelib.Data.GaussianInt.Fraction.Canonical.Height

/-! ## Canonically reduced denominator height -/

/-- Execute Gaussian Euclidean reduction followed by deterministic unit normalization.

The original displayed fraction is retained as input; the result carries the
canonical reduced integral coordinates and their exact value certificate. -/
def canonicalReduction (fraction : Fraction) :
    CanonicalFraction :=
  Canonical.reduceCanonical fraction

/-- Read denominator quadrance after executable canonical Gaussian-fraction reduction.

This natural height depends only on the exact rational value, as established by the
equality-of-values theorem. -/
def intrinsicHeight (fraction : Fraction) : Nat :=
  (canonicalReduction fraction).height

/-- Canonical Gaussian-fraction reduction preserves the original exact value. -/
theorem canonicalReduction_value (fraction : Fraction) :
    (canonicalReduction fraction).value = fraction.value :=
  Canonical.reduceCanonical_value fraction

/-- The canonically reduced Gaussian denominator has strictly positive quadrance. -/
theorem intrinsicHeight_pos (fraction : Fraction) :
    0 < intrinsicHeight fraction := by
  unfold intrinsicHeight canonicalReduction
  exact GaussianInt.normNat_pos
    (Canonical.reduceCanonical fraction).denominatorNonzero

/-- Canonical reduction never increases the displayed Gaussian denominator quadrance. -/
theorem intrinsicHeight_le_height (fraction : Fraction) :
    intrinsicHeight fraction ≤ fraction.height :=
  Canonical.reduceCanonical_height_le fraction

/-- Displayed Gaussian fractions of equal exact value have the same canonical denominator
height. -/
theorem intrinsicHeight_eq_of_value_eq
    (left right : Fraction) (valueEqual : left.value = right.value) :
    intrinsicHeight left = intrinsicHeight right :=
  Canonical.reduceCanonical_height_eq_of_value_eq
    left right valueEqual
end Purelib.Data.GaussianInt.Fraction.Canonical.Height

end
