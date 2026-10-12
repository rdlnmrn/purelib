module

import Init.Data.Fin.Basic
-- Retain the original direct finite-power instances and their executable bodies.
public import Init.GrindInstances.Ring.Fin
public import Mathlib.Algebra.Ring.Defs
-- The public nonzero-modulus binders retain the original natural zero operation.
public import Purelib.Algebra.Semiring.Nat
import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Multiplication

/-!
# Original arithmetic and commutative-ring certificates on finite residues

The original Fin carrier retains its bounded natural values, modular addition,
multiplication and negation. Direct remainder transports supply the ring laws;
the original default powers, scalar actions, subtraction and casts stay unchanged.
-/

open Purelib.Data.Nat

namespace Purelib.Algebra.Modular.Fin

public section

/-- Modular addition is associative on the original bounded residue carrier.

Reducing an intermediate addend leaves the final original remainder unchanged.
Natural associativity then compares the same three retained residue values. -/
theorem fin_add_assoc {modulus : Nat} (first second third : Fin modulus) :
    (first + second) + third = first + (second + third) := by
  apply Fin.ext
  change ((first.val + second.val) % modulus + third.val) % modulus =
    (first.val + (second.val + third.val) % modulus) % modulus
  rw [Remainder.Arithmetic.add_mod_left, Remainder.Arithmetic.add_mod_right,
    Nat.add_assoc]

/-- Swapping two original finite residues preserves their modular sum.

The same retained natural representatives are added before the original
remainder operation. Their direct scalar commutativity supplies the equality. -/
theorem fin_add_comm {modulus : Nat} (first second : Fin modulus) :
    first + second = second + first := by
  apply Fin.ext
  exact congrArg (fun value : Nat => value % modulus) (Nat.add_comm first.val second.val)

/-- Zero is a left additive identity for finite residues with nonzero modulus.

The original zero residue is its zero remainder. Removing that intermediate
reduction and using the retained representative bound recovers the same value. -/
theorem fin_zero_add {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    0 + value = value := by
  apply Fin.ext
  change (0 % modulus + value.val) % modulus = value.val
  rw [Remainder.Arithmetic.add_mod_left, Nat.zero_add]
  exact Remainder.mod_eq_of_lt value.isLt

/-- Zero is a right additive identity for the original finite residue addition.

Commutativity moves the same original zero residue to the left. The retained
left-identity certificate then recovers the unchanged finite value. -/
theorem fin_add_zero {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    value + 0 = value := (fin_add_comm value 0).trans (fin_zero_add value)

/-- Modular multiplication is associative on the original bounded residue carrier.

Each intermediate factor can be reduced before the final original remainder.
Direct natural associativity compares the same three retained representatives. -/
theorem fin_mul_assoc {modulus : Nat} (first second third : Fin modulus) :
    (first * second) * third = first * (second * third) := by
  apply Fin.ext
  change ((first.val * second.val) % modulus * third.val) % modulus =
    (first.val * ((second.val * third.val) % modulus)) % modulus
  rw [Remainder.Arithmetic.mul_mod_left, Remainder.Arithmetic.mul_mod_right,
    Multiplication.mul_assoc]

/-- Swapping two original finite residues preserves their modular product.

The same two retained natural representatives are multiplied before the
original remainder operation. Natural commutativity supplies their equality. -/
theorem fin_mul_comm {modulus : Nat} (first second : Fin modulus) :
    first * second = second * first := by
  apply Fin.ext
  exact congrArg (fun value : Nat => value % modulus) (Nat.mul_comm first.val second.val)

/-- One is a left multiplicative identity for finite residues with nonzero modulus.

The original unit is the remainder of one, including the one-element carrier.
Removing its intermediate reduction and using the original representative bound
recovers the unchanged finite value. -/
theorem fin_one_mul {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    1 * value = value := by
  apply Fin.ext
  change (1 % modulus * value.val) % modulus = value.val
  rw [Remainder.Arithmetic.mul_mod_left, Nat.one_mul]
  exact Remainder.mod_eq_of_lt value.isLt

/-- One is a right multiplicative identity for the original finite residue product.

Commutativity moves the same original unit residue to the left. Its direct
left-identity certificate recovers the unchanged retained finite value. -/
theorem fin_mul_one {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    value * 1 = value := (fin_mul_comm value 1).trans (fin_one_mul value)

/-- The original negation cancels a finite residue on the left.

Its value is the original remainder of modulus minus the retained representative.
The representative bound reconstructs one complete modulus after addition,
and that original modulus multiple has zero remainder. -/
theorem fin_neg_add_cancel {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    -value + value = 0 := by
  apply Fin.ext
  change ((modulus - value.val) % modulus + value.val) % modulus = 0 % modulus
  rw [Remainder.Arithmetic.add_mod_left, Nat.add_comm (modulus - value.val) value.val,
    Subtraction.add_sub_of_le (Nat.le_of_lt value.isLt)]
  have originalMultiple := Remainder.mul_add_mod modulus 1 0
  rw [Nat.mul_one, Nat.add_zero] at originalMultiple
  exact originalMultiple

/-- Multiplying the original residue sum distributes over its two original terms.

The intermediate modular sum and each intermediate product retain the same
natural representatives. Direct natural distributivity identifies their final
original remainders after the scalar reduction transports. -/
theorem fin_left_distrib {modulus : Nat} (first second third : Fin modulus) :
    first * (second + third) = first * second + first * third := by
  apply Fin.ext
  change (first.val * ((second.val + third.val) % modulus)) % modulus =
    ((first.val * second.val) % modulus + (first.val * third.val) % modulus) % modulus
  rw [Remainder.Arithmetic.mul_mod_right, Remainder.Arithmetic.add_mod_left,
    Remainder.Arithmetic.add_mod_right, Multiplication.left_distrib]

/-- Multiplying on the right distributes over the original residue sum.

Commutativity and the retained left-distribution certificate compare the same
three bounded residues. Each product keeps its original modular operation. -/
theorem fin_right_distrib {modulus : Nat} (first second third : Fin modulus) :
    (first + second) * third = first * third + second * third := by
  calc
    (first + second) * third = third * (first + second) := fin_mul_comm _ _
    _ = third * first + third * second := fin_left_distrib _ _ _
    _ = first * third + second * third := by rw [fin_mul_comm third first, fin_mul_comm third second]

/-- Multiplication by the original zero residue on the left gives that same zero.

Reducing the zero factor and multiplying its original representative both
produce zero before the unchanged final remainder operation. -/
theorem fin_zero_mul {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    0 * value = 0 := by
  apply Fin.ext
  change (0 % modulus * value.val) % modulus = 0 % modulus
  rw [Remainder.Arithmetic.mul_mod_left, Nat.zero_mul]

/-- Multiplication by the original zero residue on the right gives that same zero.

Commutativity moves the retained zero factor to the left. The original
left-zero certificate then identifies the same finite residue result. -/
theorem fin_mul_zero {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    value * 0 = 0 := (fin_mul_comm value 0).trans (fin_zero_mul value)

/-- The original finite-residue square is its original self-product.

The retained direct power procedure takes two original recursive steps.
Its unit factor cancels through the same finite left-identity certificate,
leaving the original two occurrences of the supplied residue. -/
theorem fin_pow_two {modulus : Nat} [NeZero modulus] (value : Fin modulus) :
    value ^ 2 = value * value := by
  rw [Lean.Grind.Fin.pow_succ, Lean.Grind.Fin.pow_succ,
    Lean.Grind.Fin.pow_zero, fin_one_mul]

end

/-- Equip the original finite residues with direct commutative-ring certificates.

The nonzero modulus retains the same original Fin operations and all original
class defaults for powers, scalar actions, subtraction and casts. Only their
proof laws are supplied by the displayed constructive scalar certificates. -/
@[expose, reducible] public def finCommRing (modulus : Nat) [NeZero modulus] : CommRing (Fin modulus) where
  add := Fin.add
  mul := Fin.mul
  neg := (Fin.neg modulus).neg
  zero := (0 : Fin modulus)
  one := (1 : Fin modulus)
  nsmul := @nsmulRecAuto (Fin modulus)
    { add := Fin.add, add_assoc := fin_add_assoc } ⟨0⟩
  npow := @npowRecAuto (Fin modulus)
    { mul := Fin.mul, mul_assoc := fin_mul_assoc } ⟨1⟩
  zsmul := zsmulRec nsmulRec
  sub := fun left right => left + -right
  add_assoc := fin_add_assoc
  add_comm := fin_add_comm
  zero_add := fin_zero_add
  add_zero := fin_add_zero
  neg_add_cancel := fin_neg_add_cancel
  mul_assoc := fin_mul_assoc
  mul_comm := fin_mul_comm
  one_mul := fin_one_mul
  mul_one := fin_mul_one
  left_distrib := fin_left_distrib
  right_distrib := fin_right_distrib
  zero_mul := fin_zero_mul
  mul_zero := fin_mul_zero

end Purelib.Algebra.Modular.Fin
