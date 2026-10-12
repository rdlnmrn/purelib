module

-- The public binary certificates retain the original natural-power wrapper.
public import Mathlib.Tactic.NormNum.Pow
-- The exponent certificate retains this structure's ordinary natural cast.
public import Purelib.Algebra.Semiring.Nat
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Multiplication

namespace Purelib.Tactic.NormNum.Natural

open Purelib.Algebra Mathlib.Meta.NormNum
open Purelib.Data.Nat

/-- A natural number certifies its own retained natural value.

The scalar and its ordinary natural cast are identical. The certificate
retains the natural semiring's original identity cast. -/
public theorem isNat_self (value : Nat) :
    @IsNat Nat Semiring.Nat.commSemiring.toSemiring.toAddMonoidWithOne value value :=
  ⟨rfl⟩

/-- Casting a retained natural value preserves its displayed numeral certificate.

The supplied certificate uses the original identity cast on natural numbers.
Transporting that scalar equality through the target's natural cast retains
the same value and numeral in its additive monoid with one. -/
public theorem isNat_natCast {R : Type*} [AddMonoidWithOne R] (value numeral : Nat)
    (certificate : @IsNat Nat Semiring.Nat.commSemiring.toSemiring.toAddMonoidWithOne
      value numeral) : IsNat (value : R) numeral := by
  obtain ⟨readback⟩ := certificate
  exact ⟨congrArg (fun retained : Nat => (retained : R)) readback⟩

/-- The computed first natural power is its retained base.

The original recursive power operation multiplies the zeroth power by the
base. Natural left-unit multiplication identifies that retained value. -/
public theorem natPow_one {a : Nat} : Nat.pow a 1 = a :=
  Nat.one_mul a

/-- Run a retained natural-power certificate from the first-power identity.

The original binary certificate consumes equality of the first power with
its base. The retained conclusion certifies the same natural power operation. -/
public theorem natPow_run {a b c : Nat}
    (certificate : IsNatPowT (Nat.pow a 1 = a) a b c) : Nat.pow a b = c :=
  certificate.run' natPow_one

/-- Squaring a retained natural power certifies twice its exponent.

The original binary-power wrapper retains its premise and computed square.
The certificate factors the doubled exponent into two equal natural powers. -/
public theorem natPow_bit0 {a b c : Nat} :
    IsNatPowT (Nat.pow a b = c) a (2 * b) (Nat.mul c c) :=
  ⟨fun power => by
    calc
      Nat.pow a (2 * b) = Nat.pow a (b + b) := congrArg (Nat.pow a) (Nat.two_mul b)
      _ = Nat.pow a b * Nat.pow a b :=
        @_root_.pow_add Nat Semiring.Nat.commSemiring.toCommMonoid.toMonoid a b b
      _ = c * c := congrArg₂ Nat.mul power power⟩

/-- Squaring a retained natural power and multiplying its base certifies an odd exponent.

The original binary-power wrapper retains its premise and computed product.
The exponent is twice the retained exponent plus one, with the same base. -/
public theorem natPow_bit1 {a b c : Nat} :
    IsNatPowT (Nat.pow a b = c) a (2 * b + 1) (Nat.mul c (Nat.mul c a)) :=
  ⟨fun power => by
    calc
      Nat.pow a (2 * b + 1) = Nat.pow a ((b + b) + 1) :=
        congrArg (Nat.pow a) (congrArg (fun value => value + 1) (Nat.two_mul b))
      _ = (Nat.pow a b * Nat.pow a b) * a := by
        change Nat.pow a (b + b) * a = (Nat.pow a b * Nat.pow a b) * a
        exact congrArg (fun value => value * a)
          (@_root_.pow_add Nat Semiring.Nat.commSemiring.toCommMonoid.toMonoid a b b)
      _ = (c * c) * a := congrArg (fun value => value * a) (congrArg₂ Nat.mul power power)
      _ = c * (c * a) := Multiplication.mul_assoc c c a⟩

/-- Natural-value certificates and a computed natural sum certify addition. -/
public theorem isNat_add {R : Type*} [AddMonoidWithOne R] :
    ∀ {f : R → R → R} {a b : R} {a' b' c : Nat},
      f = HAdd.hAdd → IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (a + b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(NatCast.add _ _).symm⟩

/-- Natural-value certificates and a computed natural product certify multiplication. -/
public theorem isNat_mul {R : Type*} [Semiring R] :
    ∀ {f : R → R → R} {a b : R} {a' b' c : Nat},
      f = HMul.hMul → IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(NatCast.mul _ _).symm⟩

/-- Natural-value certificates and a computed natural power certify exponentiation. -/
public theorem isNat_pow {R : Type*} [Semiring R] :
    ∀ {f : R → Nat → R} {a : R} {b a' b' c : Nat},
      f = HPow.hPow → IsNat a a' →
      @IsNat Nat Semiring.Nat.commSemiring.toSemiring.toAddMonoidWithOne b b' →
      Nat.pow a' b' = c → IsNat (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(NatCast.pow _ _).symm⟩

end Purelib.Tactic.NormNum.Natural
