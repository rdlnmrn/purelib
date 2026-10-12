module

meta import Purelib.Elab.Deriving.Repr

/-!
# Formal signs and their finite arithmetic

The three signs have executable equality, negation and multiplication. Their
integer readings and natural jumps are certified by direct constructor cases.
-/

@[expose] public section

namespace Purelib.Data

-- The retained nominal carrier is Purelib.Data.Sign.Basic.Sign; preserve its public constructor API.
/-- The three formal signs: negative, zero, and positive.

Equality compares constructors. A formal sign carries no scalar magnitude or
choice of a representative value. -/
inductive Sign where
  /-- The formal negative sign. -/ | negative
  /-- The formal zero sign. -/ | zero
  /-- The formal positive sign. -/ | positive
deriving DecidableEq

derive_exposed_repr Sign

namespace Sign

-- These operations retain the original Purelib.Data.Sign.Basic.Sign public owner.

/-- Read a formal sign as the integer minus one, zero, or one. -/
def value : Sign → Int
  | negative => -1
  | zero => 0
  | positive => 1

set_option backward.match.sparseCases false in
/-- Multiply two formal signs by their finite sign table.

Zero is absorbing, positive leaves the other sign unchanged, and two negative
signs multiply to positive. -/
def mul : Sign → Sign → Sign
  | zero, _ => zero
  | _, zero => zero
  | positive, y => y
  | x, positive => x
  | negative, negative => positive

/-- Reverse negative and positive signs while preserving zero. -/
def neg : Sign → Sign
  | negative => positive
  | zero => zero
  | positive => negative

/-- Compute the natural distance between the integer readings of two signs. -/
def jump (x y : Sign) : Nat := (x.value - y.value).natAbs

end Sign
end Purelib.Data

end

public section

namespace Purelib.Data.Sign
section Sign

-- These operations retain the original Purelib.Data.Sign.Basic.Sign public owner.

/-- The integer reading uniquely identifies a formal sign.

Distinct constructors have distinct readings among minus one, zero and one.
Constructor comparison therefore recovers the original sign from its reading. -/
theorem value_injective : Function.Injective value := by
  intro x y equal
  cases x <;> cases y
  · rfl
  · exact ((by decide : (-1 : Int) ≠ 0) equal).elim
  · exact ((by decide : (-1 : Int) ≠ 1) equal).elim
  · exact ((by decide : (0 : Int) ≠ -1) equal).elim
  · rfl
  · exact ((by decide : (0 : Int) ≠ 1) equal).elim
  · exact ((by decide : (1 : Int) ≠ -1) equal).elim
  · exact ((by decide : (1 : Int) ≠ 0) equal).elim
  · rfl

/-- Reading a product gives the product of the integer readings.

All nine entries of the sign table agree with multiplication of the corresponding
integers. -/
@[simp] theorem value_mul (x y : Sign) :
    value (mul x y) = value x * value y := by
  cases x <;> cases y <;> decide

/-- Reading a negated sign negates its integer reading. -/
@[simp] theorem value_neg (x : Sign) : value (neg x) = -value x := by
  cases x <;> decide

/-- A sign jump equals the jump from positive to the sign product.

The equality holds whenever at least one of the signs is nonzero. The pair of
zero signs is excluded because its product jump is one rather than zero. -/
theorem jump_eq_positive_mul (x y : Sign) (nonzero : x ≠ zero ∨ y ≠ zero) :
    jump x y = jump positive (mul x y) := by
  cases x <;> cases y
  · decide
  · decide
  · decide
  · decide
  · exact nonzero.elim (fun impossible => (impossible rfl).elim)
      (fun impossible => (impossible rfl).elim)
  · decide
  · decide
  · decide
  · decide

/-- Negating a nonzero formal sign preserves nonzeroness. -/
theorem neg_ne_zero {a : Sign} (nonzero : a ≠ zero) : neg a ≠ zero := by
  cases a
  · decide
  · exact (nonzero rfl).elim
  · decide

/-- Multiplying two nonzero formal signs preserves nonzeroness.

The only nonzero signs are negative and positive; their four products are again
negative or positive. -/
theorem mul_ne_zero {x y : Sign} (xNonzero : x ≠ zero) (yNonzero : y ≠ zero) :
    mul x y ≠ zero := by
  cases x <;> cases y
  · decide
  · exact (yNonzero rfl).elim
  · decide
  · exact (xNonzero rfl).elim
  · exact (xNonzero rfl).elim
  · exact (xNonzero rfl).elim
  · decide
  · exact (yNonzero rfl).elim
  · decide

/-- Reverse an equality to the negation of a sign.

Negation exchanges the two nonzero constructors and fixes zero, so the original
pair of signs satisfies the reversed equation as well. -/
theorem eq_neg_of_eq_neg {x y : Sign} (equal : x = Sign.neg y) :
    y = Sign.neg x := by
  cases x <;> cases y <;> cases equal <;> rfl

end Sign
end Purelib.Data.Sign

end
