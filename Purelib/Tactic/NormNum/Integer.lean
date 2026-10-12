module
import Purelib.Algebra.Ring.IntCast
-- Integer-value certificate types retain the original executable integer cast record.
public import Purelib.Algebra.Ring.Int
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Remainder
-- The exponent certificate retains the ordinary natural cast.
public import Purelib.Algebra.Semiring.Nat

import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
public import Mathlib.Tactic.NormNum.Result

open Mathlib.Meta

/-!
# Integer normalization certificates

These certificates combine retained integer values with exact computed
negations, products and powers. The cast equations use displayed sign cases
and the ring's retained operations. The ring frontend inserts these original
certificates into its generated proof before kernel checking.
-/

public section

namespace Purelib.Tactic.NormNum.Integer

open Purelib.Algebra

-- Keep the ring's original negation instead of a derived shortcut instance.
attribute [local instance high] SubNegMonoid.toNeg

/-- A natural-value certificate also certifies the displayed integer natural. -/
theorem isNat_to_isInt {R : Type*} [Ring R] :
    ∀ {a : R} {value : Nat},
      NormNum.IsNat a value → NormNum.IsInt a (.ofNat value)
  | _, value, ⟨rfl⟩ => ⟨(AddGroupWithOne.intCast_ofNat value).symm⟩

/-- A displayed natural integer-value certificate certifies the same natural value. -/
theorem isInt_to_isNat {R : Type*} [Ring R] :
    ∀ {a : R} {value : Nat},
      NormNum.IsInt a (.ofNat value) → NormNum.IsNat a value
  | _, value, ⟨rfl⟩ => ⟨AddGroupWithOne.intCast_ofNat value⟩

-- See Mathlib's note [norm_num lemma function equality].
/-- Integer-value certificates and a computed integer sum certify addition. -/
theorem isInt_add {R : Type*} [Ring R] :
    ∀ {f : R → R → R} {a b : R} {a' b' c : Int},
      f = HAdd.hAdd →
      NormNum.IsInt a a' → NormNum.IsInt b b' →
      Int.add a' b' = c → NormNum.IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Ring.IntCast.add _ _).symm⟩

-- See Mathlib's note [norm_num lemma function equality].
/-- An integer-value certificate and a computed integer negation certify negation. -/
theorem isInt_neg {R : Type*} [Ring R] :
    ∀ {f : R → R} {a : R} {a' b : Int},
      f = Neg.neg → NormNum.IsInt a a' → Int.neg a' = b →
      NormNum.IsInt (-a) b
  | _, _, _, _, rfl, ⟨rfl⟩, rfl => ⟨(Ring.IntCast.neg _).symm⟩

-- See Mathlib's note [norm_num lemma function equality].
/-- Integer-value certificates and a computed integer product certify multiplication. -/
theorem isInt_mul {R : Type*} [Ring R] :
    ∀ {f : R → R → R} {a b : R} {a' b' c : Int},
      f = HMul.hMul →
      NormNum.IsInt a a' →
      NormNum.IsInt b b' →
      Int.mul a' b' = c →
      NormNum.IsInt (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl =>
      ⟨(Ring.IntCast.intCast_mul _ _).symm⟩

-- See Mathlib's note [norm_num lemma function equality].
/-- An integer-value certificate and a computed integer power certify exponentiation. -/
theorem isInt_pow {R : Type*} [Ring R] :
    ∀ {f : R → Nat → R} {a : R} {b : Nat} {a' : Int} {b' : Nat} {c : Int},
      f = HPow.hPow →
      NormNum.IsInt a a' →
      @NormNum.IsNat Nat Semiring.Nat.commSemiring.toSemiring.toAddMonoidWithOne b b' →
      Int.pow a' b' = c →
      NormNum.IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl =>
      ⟨(Ring.IntCast.intCast_pow _ _).symm⟩

end Purelib.Tactic.NormNum.Integer

namespace Purelib.Tactic.NormNum.Integer

open Purelib.Algebra Purelib.Data.Int Purelib.Data.Nat

/-- A natural-value certificate for an integer certifies its cast into the retained ring.

The input certificate identifies the original integer with its displayed natural
cast. Scalar transport through the supplied integer cast and the ring's original
cast-of-natural law give the same natural value in that ring.
-/
theorem isNat_intCast {R : Type*} [Ring R] (integer : Int) (natural : Nat) :
    NormNum.IsNat integer natural → NormNum.IsNat (integer : R) natural := by
  intro certificate
  refine ⟨?_⟩
  exact (congrArg (fun value : Int => (value : R)) certificate.out).trans
    (AddGroupWithOne.intCast_ofNat natural)

/-- An integer-value certificate certifies the same displayed integer cast.

The retained input equality is transported through the supplied ring's integer
cast. The original integer, computed value and cast operations are unchanged.
-/
theorem isintCast {R : Type*} [Ring R] (integer value : Int) :
    NormNum.IsInt integer value → NormNum.IsInt (integer : R) value := by
  intro certificate
  refine ⟨?_⟩
  exact congrArg (fun current : Int => (current : R)) certificate.out

/-- A computed half-exponent power certifies an even power of a negative integer.

The retained exponent is twice the half exponent, and the retained magnitude
is its computed power squared. The certificate uses the original integer power. -/
theorem intPow_negOfNat_bit0
    {a b c b' c' : Nat} (power : Nat.pow a b' = c')
    (exponent : 2 * b' = b) (magnitude : c' * c' = c) :
    Int.pow (Int.negOfNat a) b = Int.ofNat c := by
  have even : b % 2 = 0 := by
    rw [← exponent]
    exact Remainder.mul_add_mod 2 b' 0
  rw [Arithmetic.pow_negOfNat, if_pos even]
  apply congrArg Int.ofNat
  calc
    Nat.pow a b = Nat.pow a (b' + b') := congrArg (Nat.pow a)
      (exponent.symm.trans (Nat.two_mul b'))
    _ = Nat.pow a b' * Nat.pow a b' :=
      @_root_.pow_add Nat Semiring.Nat.commSemiring.toCommMonoid.toMonoid a b' b'
    _ = c' * c' := congrArg₂ Nat.mul power power
    _ = c := magnitude

/-- A computed half-exponent power certifies an odd power of a negative integer.

The retained exponent is twice the half exponent plus one. The retained
magnitude multiplies its computed square by the original natural base. -/
theorem intPow_negOfNat_bit1
    {a b c b' c' : Nat} (power : Nat.pow a b' = c')
    (exponent : 2 * b' + 1 = b) (magnitude : c' * (c' * a) = c) :
    Int.pow (Int.negOfNat a) b = Int.negOfNat c := by
  have odd : b % 2 = 1 := by
    rw [← exponent]
    exact Remainder.mul_add_mod 2 b' 1
  have notEven : ¬b % 2 = 0 := fun even => Nat.noConfusion (odd.symm.trans even)
  rw [Arithmetic.pow_negOfNat, if_neg notEven]
  apply congrArg Int.negOfNat
  calc
    Nat.pow a b = Nat.pow a ((b' + b') + 1) :=
      congrArg (Nat.pow a)
        (exponent.symm.trans (congrArg (fun value => value + 1) (Nat.two_mul b')))
    _ = (Nat.pow a b' * Nat.pow a b') * a := by
      change Nat.pow a (b' + b') * a = (Nat.pow a b' * Nat.pow a b') * a
      exact congrArg (fun value => value * a)
        (@_root_.pow_add Nat Semiring.Nat.commSemiring.toCommMonoid.toMonoid a b' b')
    _ = (c' * c') * a := congrArg (fun value => value * a)
      (congrArg₂ Nat.mul power power)
    _ = c' * (c' * a) := Multiplication.mul_assoc c' c' a
    _ = c := magnitude
end Purelib.Tactic.NormNum.Integer

end
