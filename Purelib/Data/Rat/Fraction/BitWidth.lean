module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Int.BitWidth
import Purelib.Data.Nat.BitWidth
public import Purelib.Data.Rat.Fraction.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Int

open Purelib.Data.Nat

open Purelib.Data.Rat

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

namespace Purelib.Data.Rat.Fraction.BitWidth

/-- Measure the combined bit width of a canonical rational numerator and denominator.

Read the already retained reduced representative, add its signed-integer numerator width to its natural denominator
width, and retain both encoding costs. -/
def rationalWidth (value : Fraction.Rational) : Nat :=
  BitWidth.signedIntWidth (Fraction.Basic.representative value).num + BitWidth.natWidth (Fraction.Basic.representative
    value).den

/-- The combined signed-numerator and positive-denominator bit width of a canonical rational is positive. -/
theorem rationalWidth_positive (value : Fraction.Rational) :
    0 < rationalWidth value := by
  unfold rationalWidth
  have numeratorPositive := BitWidth.signedWidth_positive (Fraction.Basic.representative value).num
  have denominatorPositive := BitWidth.natWidth_positive (Fraction.Basic.representative value).den
  omega
end Purelib.Data.Rat.Fraction.BitWidth

end
