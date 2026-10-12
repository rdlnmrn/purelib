module

public import Mathlib.Algebra.Group.Defs
-- The exposed group retains the direct integer arithmetic proof fields.
public import Purelib.Data.Int.Arithmetic

namespace Purelib.Algebra.Group.Int

open Purelib.Data.Int

/-- Ordinary integer addition and scalar multiplication form a commutative group.

Natural and integer scalar multiplication retain the original integer product.
The structural arithmetic laws supply the group equations without changing
addition, subtraction, negation or either scalar multiplication operation. -/
@[expose, reducible] public def addCommGroup : AddCommGroup Int where
  add := Int.add
  zero := 0
  neg := Int.neg
  sub := Int.sub
  add_assoc := Arithmetic.add_assoc
  add_comm := Arithmetic.add_comm
  zero_add := Arithmetic.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Arithmetic.neg_add_cancel
  nsmul count value := Int.ofNat count * value
  nsmul_zero := Arithmetic.zero_mul
  nsmul_succ := Arithmetic.ofNat_succ_mul
  zsmul count value := count * value
  zsmul_zero' := Arithmetic.zero_mul
  zsmul_succ' := Arithmetic.ofNat_succ_mul
  zsmul_neg' count value := Arithmetic.neg_mul (Int.ofNat (count + 1)) value
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

/-- The original integer additive group is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def addGroup : AddGroup Int := addCommGroup.toAddGroup

/-- The original integer commutative additive monoid is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def addCommMonoid : AddCommMonoid Int := addCommGroup.toAddCommMonoid

/-- The original integer additive monoid is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def addMonoid : AddMonoid Int := addCommGroup.toAddGroup.toAddMonoid

/-- The original integer commutative additive semigroup is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def addCommSemigroup : AddCommSemigroup Int :=
  addCommGroup.toAddCommMonoid.toAddCommSemigroup

/-- The original integer additive semigroup is retained by its parent view.

This reducible projection keeps the original integer operations and complete
structural record. Ordinary instance synthesis selects that same certificate;
explicitly supplied local records of this class retain precedence. -/
@[expose, reducible] public def addSemigroup : AddSemigroup Int :=
  addCommGroup.toAddCommMonoid.toAddCommSemigroup.toAddSemigroup

-- Register the original integer records and their exact parent views.
attribute [instance 1001] addCommGroup addGroup addCommMonoid addMonoid addCommSemigroup addSemigroup

end Purelib.Algebra.Group.Int
