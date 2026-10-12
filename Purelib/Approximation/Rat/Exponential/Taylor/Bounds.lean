module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Nat.Factorial.Basic
import Purelib.Data.Nat.Factorial.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Geometric.Bounds

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Basic

section
public section

/-! Approximation Rat Exponential Taylor Bounds and its finite structural certificates. -/

namespace Purelib.Approximation.Rat.Exponential.Taylor.Bounds

open Purelib
open Purelib.Data.Nat
open Purelib.Data.Rat

/-- A finite scalar exponential term on the interval from zero to four thirds is bounded by twice a two-thirds power.

The estimate uses the displayed successor factorial and holds at every natural index. -/
theorem scalarExponentialTerm_bound {value : Fraction.Rational}
    (nonnegative : 0 ≤ value) (upper : value ≤ 4 / 3) (index : Nat) :
    (1 / (Factorial.Basic.factorial
        (index + 1) : Fraction.Rational)) * value ^ (index + 1) ≤
      2 * (2 / 3 : Fraction.Rational) ^ (index + 1) := by
  have valuePowerNonnegative : 0 ≤ value ^ (index + 1) :=
    Fraction.Order.Arithmetic.pow_nonneg_direct nonnegative _
  have upperPower := Fraction.Order.Arithmetic.pow_le_pow_direct
    nonnegative upper (index + 1)
  have factorialPositive :
      0 < (Factorial.Basic.factorial
        (index + 1) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (Factorial.Basic.factorial_pos (index + 1))
  have twoPowerPositive : 0 < (2 : Fraction.Rational) ^ index :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) index
  have denominatorOrder :
      (2 : Fraction.Rational) ^ index ≤
        (Factorial.Basic.factorial
          (index + 1) : Fraction.Rational) := by
    have castOrder := Fraction.Cast.Order.natCast_le_direct
      (Factorial.Bounds.two_pow_le_factorial_succ index)
    have castPower : ((Nat.pow 2 index : Nat) : Fraction.Rational) = (2 : Fraction.Rational) ^ index := by
      change (((2 ^ index : Nat) : Fraction.Rational)) = _
      simpa only [Nat.cast_ofNat] using (Purelib.Algebra.NatCast.pow (R := Fraction.Rational) 2 index)
    rewrite [castPower] at castOrder
    exact castOrder
  calc
    (1 / (Factorial.Basic.factorial
          (index + 1) : Fraction.Rational)) * value ^ (index + 1) =
        value ^ (index + 1) /
          (Factorial.Basic.factorial
            (index + 1) : Fraction.Rational) := by
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
        Algebra.Field.ExplicitField.div_eq_mul_inv,
        Fraction.Field.one_mul,
        Fraction.Field.mul_comm]
    _ ≤ (4 / 3 : Fraction.Rational) ^ (index + 1) /
          (Factorial.Basic.factorial
            (index + 1) : Fraction.Rational) := by
      apply (Fraction.Order.Field.div_le_iff_pos
        factorialPositive).mpr
      calc
        value ^ (index + 1) ≤ (4 / 3 : Fraction.Rational) ^ (index + 1) := upperPower
        _ = ((4 / 3 : Fraction.Rational) ^ (index + 1) /
              (Factorial.Basic.factorial
                (index + 1) : Fraction.Rational)) *
            (Factorial.Basic.factorial
              (index + 1) : Fraction.Rational) := by
          exact (Fraction.Field.div_mul_cancel_of_ne _ _
            factorialPositive.ne').symm
    _ ≤ (4 / 3 : Fraction.Rational) ^ (index + 1) /
          (2 : Fraction.Rational) ^ index :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
        twoPowerPositive denominatorOrder
    _ = 2 * (2 / 3 : Fraction.Rational) ^ (index + 1) :=
      Geometric.Bounds.fourThird_div_twoPow index
end Purelib.Approximation.Rat.Exponential.Taylor.Bounds

end
