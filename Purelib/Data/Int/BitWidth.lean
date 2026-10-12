module

public import Purelib.Data.Nat.BitWidth
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.Nat

section
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

namespace Purelib.Data.Int.BitWidth

/-- Charge an integer its natural magnitude width plus one sign bit.

The magnitude width is the retained natWidth of its natural absolute value; this
signed width includes an additional bit even at zero. -/
def signedIntWidth (value : Int) : Nat := BitWidth.natWidth value.natAbs + 1
end Purelib.Data.Int.BitWidth

end

end

section
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

namespace Purelib.Data.Int.BitWidth

open Purelib.Data.Int in
/-- The signed integer width is strictly positive. -/
theorem signedWidth_positive (value : Int) : 0 < signedIntWidth value := by
  unfold signedIntWidth
  omega
end Purelib.Data.Int.BitWidth

end

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Int.BitWidth

/-- Measure an integer by the natural binary width of its absolute value.

This operation uses natWidth directly and adds no extra sign-bit charge beyond the
width convention already built into natWidth. -/
def intWidth (value : Int) : Nat := BitWidth.natWidth value.natAbs
end Purelib.Data.Int.BitWidth

end
