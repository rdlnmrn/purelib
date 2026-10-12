module

public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Rational rectangular side lengths

The ordered real and imaginary endpoints determine the original horizontal
and vertical widths. Their retained order certificates make both widths nonnegative.
-/

open Purelib.Data.Rat

namespace Purelib.Geometry.Rational.Box

/-- The horizontal side length, given by the difference of real endpoints.

The displayed width subtracts the original lower real endpoint from the upper
endpoint, retaining the original rational carrier and subtraction operation. -/
@[expose] public def widthX (B : Box) : Fraction.Rational := B.xUpper - B.xLower

/-- The vertical side length, given by the difference of imaginary endpoints.

The displayed width subtracts the original lower imaginary endpoint from the
upper endpoint, retaining the original rational carrier and subtraction operation. -/
@[expose] public def widthY (B : Box) : Fraction.Rational := B.yUpper - B.yLower

/-- Ordering of the real endpoints makes the horizontal width nonnegative.

The original box retains its lower-to-upper real endpoint comparison.
Direct rational subtraction comparison gives the width bound. -/
public theorem widthX_nonneg (B : Box) : 0 ≤ B.widthX :=
  Fraction.Order.Arithmetic.sub_nonneg_direct B.x_valid

/-- Ordering of the imaginary endpoints makes the vertical width nonnegative.

The original box retains its lower-to-upper imaginary endpoint comparison.
Direct rational subtraction comparison gives the width bound. -/
public theorem widthY_nonneg (B : Box) : 0 ≤ B.widthY :=
  Fraction.Order.Arithmetic.sub_nonneg_direct B.y_valid

end Purelib.Geometry.Rational.Box
