module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field

open Purelib.Algebra.Field

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Data.Gaussian.Constants.Inverse

/-- The squared norm of the reciprocal of one plus i is exactly one half. -/
public theorem normSq_gamma_inv : Norm.Basic.normSq Canonical.gamma⁻¹ = (1
  / 2 : Rational) := by
  rw [Field.inv_eq, Field.normSq_inv Canonical.gamma (by decide), Constants.normSq_gamma]
  change (2 : Rational)⁻¹ = 1 * (2 : Rational)⁻¹
  exact (_root_.one_mul _).symm

/-- Dividing the reciprocal of one plus i by a nonzero Gaussian equals the reciprocal of
their product. -/
theorem gamma_inv_div_eq_inverse (residual : Canonical)
    (residualNonzero : residual ≠ 0) :
    Canonical.gamma⁻¹ / residual = (Canonical.gamma * residual)⁻¹ := by
  have gammaNonzero : Canonical.gamma ≠ 0 := by decide
  have productNonzero : Canonical.gamma * residual ≠ 0 :=
    Field.mul_ne_zero_direct gammaNonzero residualNonzero
  apply Field.mul_right_cancel_of_ne productNonzero
  calc
    (Canonical.gamma⁻¹ / residual) * (Canonical.gamma * residual) =
        (Canonical.gamma⁻¹ * residual⁻¹) * (Canonical.gamma * residual) := by
      rw [ExplicitField.div_eq_mul_inv]
    _ = (Canonical.gamma⁻¹ * Canonical.gamma) * (residual⁻¹ * residual) :=
      Field.gaussian_mul_pair_swap _ _ _ _
    _ = (1 : Canonical) * 1 := by
      apply congrArg₂ (fun left right : Canonical => left * right)
      · exact Canonical.inv_mul_cancel
          Canonical.gamma gammaNonzero
      · exact Canonical.inv_mul_cancel
          residual residualNonzero
    _ = 1 := Gaussian.Basic.mul_one _
    _ = (Canonical.gamma * residual)⁻¹ * (Canonical.gamma * residual) :=
      (Canonical.inv_mul_cancel
        (Canonical.gamma * residual) productNonzero).symm
end Purelib.Data.Gaussian.Constants.Inverse

end

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.Gaussian.Constants.Inverse

/-! ## Unary normalization identities -/

/-- The Gaussian value one plus i is nonzero. -/
public theorem gamma_ne : Canonical.gamma ≠ 0 := by decide

end Purelib.Data.Gaussian.Constants.Inverse

end
