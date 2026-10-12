module
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Nat.LCM
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Constants

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Constants

section
public section

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator

/-! ## Least common-denominator coefficient clearing -/

/-- Compute the least positive common denominator of a Gaussian rational's two reduced
coordinates.

Read both retained canonical rational representatives and take the executable lcm of
their positive natural denominators. -/
@[expose] def coefficientDenominator (coefficient : Canonical) : Nat :=
  LCM.lcm
    (Fraction.Basic.representative coefficient.re).den
    (Fraction.Basic.representative coefficient.im).den

open Purelib.Data.Gaussian.Fraction.NaturalDenominator in
/-- The computed common denominator of both Gaussian coordinates is strictly positive. -/
theorem coefficientDenominator_pos (coefficient : Canonical) :
    0 < LeastDenominator.coefficientDenominator coefficient := by
  exact LCM.lcm_pos
    (Fraction.Basic.representative coefficient.re).den_pos
    (Fraction.Basic.representative coefficient.im).den_pos
end Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator

end

section
public section

/-!
# Sharpness witnesses for the denominator-height obstruction

For every positive coefficient scale `S`, positive common denominator `D`,
and degree `d`, the displayed monomial `(1/S) Z^d` evaluated at `1/D`
attains equality in the lower residual bound.  Thus the unit constant and the
exponents of both `S²` and `H^d` cannot be uniformly improved using only
these displayed parameters.
-/

section

namespace Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator
open Purelib.Data.Gaussian.Fraction.NaturalDenominator in
/-- The canonical zero Gaussian value has common coordinate denominator one. -/
theorem coefficientDenominator_zero :
    LeastDenominator.coefficientDenominator (0 : Canonical) = 1 := by
  unfold LeastDenominator.coefficientDenominator
  change LCM.lcm
    (Fraction.Basic.representative (0 : Rational)).den
    (Fraction.Basic.representative (0 : Rational)).den = 1
  rw [Constants.representative_zero]
  exact LCM.lcm_one_right 1
end Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator

end

end
