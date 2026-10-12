module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic

public import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data

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

namespace Purelib.Data.Gaussian.Inverse.Subtraction

/-- Express the difference of two nonzero Gaussian reciprocals using their product and
original difference.

The two retained nonzero hypotheses permit inverse cancellation; the result is minus
the original difference times the product of the reciprocals. -/
theorem inverse_sub_inverse {left right : Canonical}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left⁻¹ - right⁻¹ =
      -(left - right) * (left⁻¹ * right⁻¹) := by
  calc
    left⁻¹ - right⁻¹ = left⁻¹ * 1 - 1 * right⁻¹ := by
      rw [_root_.mul_one, _root_.one_mul]
    _ = left⁻¹ * (right * right⁻¹) -
        (left * left⁻¹) * right⁻¹ := by
      simp only [ExplicitField.mul_inv_cancel right rightNonzero,
        ExplicitField.mul_inv_cancel left leftNonzero, _root_.mul_one, _root_.one_mul, -eq_self, -iff_self]
      rfl
    _ = -(left - right) * (left⁻¹ * right⁻¹) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
        ring1

end Purelib.Data.Gaussian.Inverse.Subtraction

end
