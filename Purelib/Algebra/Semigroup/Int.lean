module

public import Mathlib.Algebra.Group.Defs
-- The exposed structures retain the integer arithmetic proof fields.
public import Purelib.Data.Int.Arithmetic

namespace Purelib.Algebra.Semigroup.Int

open Purelib.Data.Int

/-- Ordinary integer multiplication forms a semigroup with structural associativity.

The original integer multiplication is retained. Its direct associative law
supplies the structural certificate selected by ordinary instance synthesis;
explicitly retained local records of this class keep their precedence. -/
@[expose, reducible] public def semigroup : Semigroup Int where
  mul := Int.mul
  mul_assoc := Arithmetic.mul_assoc

/-- Ordinary integer multiplication forms a commutative semigroup.

The multiplication operation and its displayed sign cases are unchanged;
associativity and commutativity use the direct integer arithmetic laws.
Explicitly retained local records of this class keep their precedence. -/
@[expose, reducible] public def commSemigroup : CommSemigroup Int where
  toSemigroup := semigroup
  mul_comm := Arithmetic.mul_comm

-- Register the original integer multiplication records without copying fields.
attribute [instance 1001] semigroup commSemigroup

end Purelib.Algebra.Semigroup.Int
