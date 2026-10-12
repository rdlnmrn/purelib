module

public import Mathlib.Algebra.Ring.Defs
-- The exposed ring retains the original executable group and monoid fields.
public import Purelib.Algebra.Group.Int
public import Purelib.Algebra.Monoid.Int

namespace Purelib.Algebra.Ring.Int

open Purelib.Algebra Purelib.Data.Int

/-- Ordinary integer arithmetic forms a commutative ring with structural laws.

The additive group, products, powers and both casts retain their original
executable operations. Distributivity follows from the direct displayed
integer arithmetic laws. -/
@[expose, reducible] public def commRing : CommRing Int where
  toAddCommGroup := Group.Int.addCommGroup
  toCommMonoid := Monoid.Int.commMonoid
  zero_mul := Arithmetic.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Arithmetic.mul_add
  right_distrib := Arithmetic.add_mul
  natCast := Int.ofNat
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast value := value
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

/-- The original integer ring is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def ring : Ring Int := commRing.toRing

/-- The original integer commutative semiring is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def commSemiring : CommSemiring Int := commRing.toCommSemiring

/-- The original integer semiring is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def semiring : Semiring Int := commRing.toRing.toSemiring

/-- The original integer distributive multiplication is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def distrib : Distrib Int := commRing.toRing.toSemiring.toDistrib

-- Register the original integer records and their exact parent views.
attribute [instance 1001] commRing ring commSemiring semiring distrib

end Purelib.Algebra.Ring.Int
