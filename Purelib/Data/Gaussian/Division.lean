module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field

import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.CCL.Calculus.DividedDifference
namespace RationalPolynomial

end RationalPolynomial

end Purelib.CCL.Calculus.DividedDifference

end

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Data.Gaussian.Division

/-- Multiplication by the retained nonzero Gaussian denominator cancels exact division. -/
theorem gaussian_div_mul_cancel (numerator denominator : Canonical)
    (nonzero : denominator ≠ 0) :
    (numerator / denominator) * denominator = numerator := by
  rw [ExplicitField.div_eq_mul_inv,
    Gaussian.Basic.mul_assoc]
  rw [show denominator⁻¹ * denominator = 1 from
    Canonical.inv_mul_cancel denominator nonzero,
    _root_.mul_one]
end Purelib.Data.Gaussian.Division

end
