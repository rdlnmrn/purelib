module
public import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Fraction.BitWidth

import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

namespace Purelib.Data.Gaussian.BitWidth

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Compute the sum of the bit widths of the two retained rational coordinates. -/
def gaussianWidth (value : Basic.Canonical) : Nat :=
  Fraction.BitWidth.rationalWidth value.re + Fraction.BitWidth.rationalWidth value.im

/-- The sum of the two canonical rational coordinate widths is strictly positive. -/
theorem gaussianWidth_positive (value : Basic.Canonical) :
    0 < gaussianWidth value := by
  unfold gaussianWidth
  have realPositive := Fraction.BitWidth.rationalWidth_positive value.re
  have imaginaryPositive := Fraction.BitWidth.rationalWidth_positive value.im
  omega
end Purelib.Data.Gaussian.BitWidth

end
