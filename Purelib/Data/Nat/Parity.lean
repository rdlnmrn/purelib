module

public import Init.Data.Nat.Div.Basic
public import Purelib.Algebra.Semiring.Nat
import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Remainder

namespace Purelib.Data.Nat.Parity

open Purelib.Data.Nat

/-- An even natural has a displayed half whose double is that value.

The retained witness uses the original addition equation `value = half + half`.
This is the exact natural specialization of evenness, preserving the
same displayed half and its original equation. -/
@[expose, reducible] public def Even (value : Nat) : Prop :=
  ∃ half : Nat, value = half + half

/-- An odd natural has a displayed half whose doubled successor is that value.

The retained witness and its defining equation use the original natural
operations. This is the exact natural specialization of the semiring oddness
predicate, with its original witness and equality rather than a new carrier. -/
@[expose, reducible] public def Odd (value : Nat) : Prop :=
  ∃ half : Nat, value = 2 * half + 1

/-- Adding two preserves the natural remainder modulo two. -/
public theorem add_two_mod (value : Nat) : (value + 2) % 2 = value % 2 := by
  rw [Remainder.mod_eq_sub_mod (Nat.le_add_left 2 value), Nat.add_comm value 2,
    Subtraction.add_sub_cancel_left]

/-- Consecutive natural numbers have the two opposite remainders modulo two.

The first alternative displays an even value and its odd successor; the
second displays an odd value and its even successor. -/
public theorem consecutive : ∀ value : Nat,
    (value % 2 = 0 ∧ (value + 1) % 2 = 1) ∨
    (value % 2 = 1 ∧ (value + 1) % 2 = 0)
  | 0 => Or.inl ⟨rfl, rfl⟩
  | value + 1 => by
      have next : (value + 1 + 1) % 2 = value % 2 := add_two_mod value
      cases consecutive value with
      | inl even => exact Or.inr ⟨even.2, next.trans even.1⟩
      | inr odd => exact Or.inl ⟨odd.2, next.trans odd.1⟩

/-- A natural square has the same remainder modulo two as its base.

The original product is reduced by the retained scalar remainder transports.
The two explicit remainder cases then compute the same original zero or unit
remainder of that same base. -/
public theorem square_mod_two (value : Nat) : value ^ 2 % 2 = value % 2 := by
  have reduced : value ^ 2 % 2 = (value % 2 * (value % 2)) % 2 := by
    calc
      value ^ 2 % 2 = (value * value) % 2 :=
        congrArg (· % 2) (Multiplication.pow_two value)
      _ = (value % 2 * value) % 2 :=
        (Remainder.Arithmetic.mul_mod_left value value 2).symm
      _ = (value % 2 * (value % 2)) % 2 :=
        (Remainder.Arithmetic.mul_mod_right (value % 2) value 2).symm
  cases consecutive value with
  | inl even => rw [reduced, even.1]
  | inr odd => rw [reduced, odd.1]

end Purelib.Data.Nat.Parity
