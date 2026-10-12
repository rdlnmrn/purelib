module

import Purelib.Tactic.Ring

public import Purelib.Data.Int.ToNat
public import Purelib.Data.Rat.Fraction
import Purelib.Data.Int.Order
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Data

/-!
# Signed positive-denominator fraction displays

The original integer numerator and positive integer denominator retain their
cross-product equivalence. Reading the denominator as a natural constructs
the same positive raw fraction display, with its direct equality certificates.
-/

namespace Purelib.Data.Rat

open Purelib.Data.Int

@[expose] public section

set_option genInjectivity false in
/-- Retain an integer numerator and a strictly positive integer denominator.

The record stores the exact finite coordinates together with denominator positivity. -/
structure SignedFraction where
  /-- The retained signed integer numerator. -/ num : Int
  /-- The retained denominator. -/ den : Int
  /-- The retained denominator is strictly positive. -/ den_pos : 0 < den
deriving DecidableEq

constructive_injectivity SignedFraction

end

namespace SignedFraction

end SignedFraction
namespace SignedFraction.Basic

/-- Two positive-denominator displays have equal integer cross-products.

The original signed numerators are multiplied by the opposite retained
positive denominators. Equality compares those exact integer products without
normalizing either input display. -/
@[expose] public def Equivalent (left right : SignedFraction) : Prop :=
  left.num * right.den = right.num * left.den

/-- Decide cross-product equivalence by the displayed integer arithmetic. -/
public instance (left right : SignedFraction) : Decidable (Equivalent left right) :=
  inferInstanceAs
    (Decidable (left.num * right.den = right.num * left.den))

/-- Every displayed fraction is cross-product equivalent to itself. -/
public theorem equivalent_refl (fraction : SignedFraction) :
    Equivalent fraction fraction := rfl

/-- Reverse a displayed cross-product equivalence. -/
public theorem equivalent_symm {left right : SignedFraction}
    (equivalent : Equivalent left right) : Equivalent right left :=
  equivalent.symm

/-- Signed cross-multiplication equivalence composes through a positive denominator.

The middle denominator remains a nonzero common factor. Its retained positive
sign permits direct scalar cancellation after the two supplied equations. -/
public theorem equivalent_trans {left middle right : SignedFraction}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right := by
  have middleDenominatorNonzero : middle.den ≠ 0 :=
    fun zero => Order.lt_irrefl 0 (zero ▸ middle.den_pos)
  apply Arithmetic.eq_of_mul_eq_mul_left middleDenominatorNonzero
  calc
    middle.den * (left.num * right.den) = (left.num * middle.den) * right.den := by
      rw [← Arithmetic.mul_assoc, Arithmetic.mul_comm middle.den left.num]
    _ = (middle.num * left.den) * right.den := congrArg (· * right.den) leftMiddle
    _ = (middle.num * right.den) * left.den := by
      rw [Arithmetic.mul_assoc, Arithmetic.mul_comm left.den right.den, ← Arithmetic.mul_assoc]
    _ = (right.num * middle.den) * left.den := congrArg (· * left.den) middleRight
    _ = middle.den * (right.num * left.den) := by
      rw [Arithmetic.mul_comm right.num middle.den, Arithmetic.mul_assoc]

end SignedFraction.Basic
namespace SignedFraction

/-- Convert a signed display to the same numerator and a positive natural denominator.

The retained integer denominator positivity identifies it with the cast of its natural value, preserving the original
displayed fraction. -/
@[expose] public def toRaw (fraction : SignedFraction) : Fraction.RawFraction :=
  ⟨fraction.num, fraction.den.toNat, ToNat.toNat_pos_direct fraction.den_pos⟩

end SignedFraction
namespace SignedFraction.Basic

/-- Conversion to a natural denominator preserves signed cross-multiplication equivalence.

Both positive integer denominators survive natural conversion and its integer
readback, so the two displayed cross-product equations coincide. -/
public theorem fraction_toRaw_equivalent_iff (left right : SignedFraction) :
    Fraction.Equivalent left.toRaw right.toRaw ↔ Equivalent left right := by
  change (left.num * (right.den.toNat : Int) = right.num * (left.den.toNat : Int)) ↔
    left.num * right.den = right.num * left.den
  rw [ToNat.toNat_of_pos left.den_pos, ToNat.toNat_of_pos right.den_pos]

end SignedFraction.Basic
end Purelib.Data.Rat
