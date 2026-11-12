module

public import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Finite monotonicity of the original power-difference multiplier

The proof follows the original finite exponent recurrence and retains both
numeric bases. No root process, power evaluator or observation is rebuilt.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Power

open Purelib.Data.Rat

/-- Increasing a nonnegative squared-magnitude bound increases its original finite power-difference multiplier. -/
theorem differenceFactor_mono {first last : Fraction.Rational} (nonnegative : 0 ≤ first) (order : first ≤ last) :
    (exponent : Nat) → differenceFactor first exponent ≤ differenceFactor last exponent
  | 0 => Fraction.Order.Basic.le_refl _
  | exponent + 1 => by
      rewrite [differenceFactor_succ, differenceFactor_succ]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct
          (Fraction.Order.Arithmetic.mul_le_mul_direct (differenceFactor_mono nonnegative order exponent) order
            nonnegative (differenceFactor_nonnegative (nonnegative.trans order) exponent))
          (Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative order exponent))
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)

end Purelib.Data.Gaussian.Norm.Power

end
