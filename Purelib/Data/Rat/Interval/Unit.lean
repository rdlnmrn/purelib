module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace Purelib.Data.Rat.Interval.Unit

open Purelib.Data.Rat in
/-- Every natural rational cast is strictly below itself plus one. -/
public theorem unitIntervalProper (index : Nat) :
    (index : Fraction.Rational) < (index : Fraction.Rational) + 1 := by
  have added := Fraction.Order.Arithmetic.add_lt_add_left_direct
    (show (0 : Fraction.Rational) < 1 by decide) (index : Fraction.Rational)
  calc
    (index : Fraction.Rational) = (index : Fraction.Rational) + 0 := by ring1
    _ < (index : Fraction.Rational) + 1 := added

end Purelib.Data.Rat.Interval.Unit

end
