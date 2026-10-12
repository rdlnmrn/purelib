module

public import Mathlib.Algebra.Ring.Defs
-- The exposed semiring retains these structural proof fields.
public import Purelib.Data.Nat.Multiplication

namespace Purelib.Algebra.Semiring.Nat

open Purelib.Data.Nat

/-- Natural arithmetic forms a commutative semiring with structural proof laws.

Addition, multiplication, casts, repeated addition and powers are the ordinary
natural operations, including their original executable implementations. -/
@[expose, reducible] public def commSemiring : CommSemiring Nat where
  add := Nat.add
  zero := Nat.zero
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul count value := count * value
  nsmul_zero := Nat.zero_mul
  nsmul_succ := Nat.succ_mul
  mul := Nat.mul
  one := Nat.succ Nat.zero
  mul_assoc := Multiplication.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  npow exponent value := value ^ exponent
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl
  natCast value := value
  natCast_zero := rfl
  natCast_succ _ := rfl
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  left_distrib := Multiplication.left_distrib
  right_distrib := Multiplication.right_distrib

/-- Natural multiplication retains the monoid parent of its commutative semiring.

Multiplication, the unit and natural powers are the original executable
operations. The retained parent supplies their structural laws; its instance
priority replaces the original concrete monoid while preserving local owners. -/
@[expose, reducible] public def monoid : Monoid Nat :=
  commSemiring.toCommMonoid.toMonoid

attribute [instance 1001] monoid

/-- Natural addition retains the additive monoid parent of its commutative semiring.

Addition, zero and natural scalar multiplication are the original executable
operations. The retained parent supplies their structural laws; its instance
priority replaces the original concrete additive monoid while preserving local owners. -/
@[expose, reducible] public def addMonoid : AddMonoid Nat :=
  commSemiring.toAddCommMonoid.toAddMonoid

attribute [instance 1001] addMonoid

/-- Natural multiplication retains zero from its original semiring parent.

Multiplication and zero are the original executable operations. The projected
parent supplies their structural zero laws; its instance priority replaces the
original concrete proof adapter while preserving explicit local parents. -/
@[expose, reducible] public def mulZeroClass : MulZeroClass Nat :=
  commSemiring.toSemiring.toNonUnitalSemiring.toNonUnitalNonAssocSemiring.toMulZeroClass

attribute [instance 1001] mulZeroClass

end Purelib.Algebra.Semiring.Nat
