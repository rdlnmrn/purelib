module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget

/-- The input-sensitivity coefficient `16 * 4`. -/
def inputErrorScale : Fraction.Rational := 16
  * 4

/-- `2 * (10 + 16 * 4)`, kept as a small arithmetic expression so neither the kernel nor executable fraction arithmetic
expands a large unary numeral. -/
def errorScale : Fraction.Rational := 2 * (10
  + inputErrorScale)

/-- The displayed progressive exponential error scale is nonnegative. -/
theorem errorScale_nonneg : 0 ≤
  errorScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Budget

end
