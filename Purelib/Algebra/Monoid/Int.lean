module

import Mathlib.Algebra.Group.Defs
-- The exposed monoid retains the original structural semigroup fields.
public import Purelib.Algebra.Semigroup.Int

namespace Purelib.Algebra.Monoid.Int

open Purelib.Algebra Purelib.Data.Int

/-- Ordinary integer multiplication and powers form a commutative monoid.

The power field is the original executable integer power function. Its
zero and successor laws use the retained natural remainder cases. -/
@[expose, reducible] public def commMonoid : CommMonoid Int where
  toCommSemigroup := Semigroup.Int.commSemigroup
  one := 1
  one_mul := Int.one_mul
  mul_one := Arithmetic.mul_one
  npow exponent value := Int.pow value exponent
  npow_zero := Arithmetic.pow_zero
  npow_succ exponent value := Arithmetic.pow_succ value exponent

/-- The multiplicative monoid retains the same displayed integer powers. -/
@[expose, reducible] public def monoid : Monoid Int := commMonoid.toMonoid

-- Register the original integer records and their exact parent views.
attribute [instance 1001] commMonoid monoid

/-- Every natural power of minus four is a nonzero integer. -/
public theorem
  negative_four_pow_ne_zero
  : ∀ index : Nat,
    ((-4 : Int) ^ index) ≠ 0
  | 0 => by decide
  | index + 1 => by
      rw [Purelib.Data.Int.Arithmetic.pow_succ]
      intro productZero
      rcases Purelib.Data.Int.Arithmetic.eq_zero_of_mul_eq_zero productZero with previousZero | fourZero
      · exact
          Purelib.Algebra.Monoid.Int.negative_four_pow_ne_zero
          index previousZero
      · exact (by decide : (-4 : Int) ≠ 0) fourZero

end Purelib.Algebra.Monoid.Int
