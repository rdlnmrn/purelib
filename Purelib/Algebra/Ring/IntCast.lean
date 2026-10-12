module
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs

import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic
-- The public power equation retains the ordinary integer power operation.
public import Purelib.Algebra.Monoid.Int
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.NatCast
import Purelib.Algebra.Ring.Multiplication
import Purelib.Data.Int.Arithmetic

namespace Purelib.Algebra.Ring.IntCast

open Purelib.Algebra Purelib.Data.Int

-- Retain negation from the original group, with its direct zero law.
attribute [local instance high] SubNegMonoid.toNeg Group.Negation.subNegZeroMonoid

/-- Casting the displayed integer zero gives the ring zero.

The original integer cast-of-natural equation at zero identifies the retained ring zero. No cast operation or supplied
ring instance is replaced. -/
public theorem cast_zero {R : Type*} [Ring R] : ((0 : Int) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero

/-- Casting a displayed negative successor uses its retained cast equation. -/
public theorem cast_negSucc {R : Type*} [Ring R] (value : Nat) :
    ((Int.negSucc value : Int) : R) = -(value + 1 : Nat) :=
  AddGroupWithOne.intCast_negSucc value

/-- Casting a displayed negative natural negates its natural cast. -/
private theorem cast_negOfNat {R : Type*} [Ring R] (value : Nat) :
    ((Int.negOfNat value : Int) : R) = -(value : R) := by
  cases value with
  | zero =>
      change (((0 : Nat) : Int) : R) = -((0 : Nat) : R)
      rw [Nat.cast_zero (R := R)]
      exact ((AddGroupWithOne.intCast_ofNat (R := R) 0).trans (Nat.cast_zero (R := R))).trans
        (SubtractionMonoid.neg_eq_of_add (0 : R) 0 (AddZeroClass.add_zero (0 : R))).symm
  | succ value => exact AddGroupWithOne.intCast_negSucc value

/-- Casting an integer negation preserves the displayed negation. -/
public theorem neg {R : Type*} [Ring R] (value : Int) :
    ((Int.neg value : Int) : R) = -(value : R) := by
  cases value with
  | ofNat value =>
      change ((Int.negOfNat value : Int) : R) = -(((value : Nat) : Int) : R)
      rw [cast_negOfNat, Int.cast_natCast]
  | negSucc value =>
      change (((value + 1 : Nat) : Int) : R) = -((Int.negSucc value : Int) : R)
      rw [Int.cast_natCast, cast_negSucc, neg_neg]

/-- Casting addition of the displayed integer unit increments its ring cast.

Each displayed sign case uses the original cast field or the retained
additive inverse equation at the integer unit. -/
private theorem cast_add_one {R : Type*} [Ring R] (value : Int) :
    ((value + 1 : Int) : R) = (value : R) + 1 := by
  cases value with
  | ofNat value =>
      change (((value + 1 : Nat) : Int) : R) = (((value : Nat) : Int) : R) + 1
      rw [Int.cast_natCast, Int.cast_natCast, Nat.cast_succ]
  | negSucc value =>
      cases value with
      | zero =>
          change ((0 : Int) : R) = ((Int.negSucc 0 : Int) : R) + 1
          rw [cast_zero, cast_negSucc, Nat.cast_one]
          exact (AddGroup.neg_add_cancel (1 : R)).symm
      | succ value =>
          change ((Int.negSucc value : Int) : R) =
            ((Int.negSucc (value + 1) : Int) : R) + 1
          rw [cast_negSucc, cast_negSucc, Nat.cast_succ (value + 1),
            SubtractionMonoid.neg_add_rev]
          rw [add_comm (-1 : R), add_assoc, AddGroup.neg_add_cancel, add_zero]

/-- Casting a sum with a natural integer summand preserves both displayed values.

Structural induction on the retained natural summand translates one unit at
a time without changing the integer addition operation. -/
private theorem cast_add_natural {R : Type*} [Ring R] : ∀ count : Nat, ∀ value : Int,
    ((Int.ofNat count + value : Int) : R) = (count : R) + (value : R)
  | 0, value => by
      change ((0 + value : Int) : R) = ((0 : Nat) : R) + (value : R)
      rw [Arithmetic.zero_add, Nat.cast_zero (R := R), zero_add]
  | count + 1, value => by
      calc
        ((Int.ofNat (count + 1) + value : Int) : R) =
            (((Int.ofNat count + value) + 1 : Int) : R) :=
          congrArg (fun item : Int => (item : R)) (Arithmetic.add_natural_succ count value).symm
        _ = ((Int.ofNat count + value : Int) : R) + 1 := cast_add_one _
        _ = ((count : R) + (value : R)) + 1 :=
          congrArg (· + 1) (cast_add_natural count value)
        _ = ((count + 1 : Nat) : R) + (value : R) := by
          rw [Nat.cast_succ, add_assoc, add_comm (value : R) (1 : R), ← add_assoc]

/-- Integer casts preserve addition.

Natural summands use structural unit translations. A negative successor
summand uses cancellation of its retained positive magnitude on both sides. -/
public theorem add {R : Type*} [Ring R] (left right : Int) :
    ((left + right : Int) : R) = (left : R) + (right : R) := by
  cases left with
  | ofNat left =>
      change ((Int.ofNat left + right : Int) : R) =
        (((left : Nat) : Int) : R) + (right : R)
      rw [Int.cast_natCast]
      exact cast_add_natural left right
  | negSucc left =>
      have cancels : Int.ofNat (left + 1) + Int.negSucc left = 0 :=
        (Arithmetic.add_comm _ _).trans (Arithmetic.neg_add_cancel (Int.ofNat (left + 1)))
      have translated : ((left + 1 : Nat) : R) +
          ((Int.negSucc left + right : Int) : R) = (right : R) := by
        calc
          _ = ((Int.ofNat (left + 1) + (Int.negSucc left + right) : Int) : R) :=
            (cast_add_natural (left + 1) (Int.negSucc left + right)).symm
          _ = (right : R) := by
            apply congrArg (fun item : Int => (item : R))
            rw [← Arithmetic.add_assoc, cancels, Arithmetic.zero_add]
      rw [cast_negSucc]
      calc
        ((Int.negSucc left + right : Int) : R) =
            0 + ((Int.negSucc left + right : Int) : R) := (zero_add _).symm
        _ = (-((left + 1 : Nat) : R) + ((left + 1 : Nat) : R)) +
            ((Int.negSucc left + right : Int) : R) :=
          congrArg (· + ((Int.negSucc left + right : Int) : R))
            (AddGroup.neg_add_cancel _).symm
        _ = -((left + 1 : Nat) : R) +
            (((left + 1 : Nat) : R) + ((Int.negSucc left + right : Int) : R)) :=
          add_assoc _ _ _
        _ = -((left + 1 : Nat) : R) + (right : R) :=
          congrArg (-((left + 1 : Nat) : R) + ·) translated

/-- Integer casts preserve subtraction of the two displayed values.

Integer subtraction is the original addition of a negated right operand.
Its retained addition and negation certificates identify the ring subtraction
without changing either integer or the supplied ring operations. -/
public theorem sub {R : Type*} [Ring R] (left right : Int) :
    ((left - right : Int) : R) = (left : R) - (right : R) := by
  change ((left + Int.neg right : Int) : R) = (left : R) - (right : R)
  exact (add left (Int.neg right)).trans
    ((congrArg (fun operand : R => (left : R) + operand) (neg right)).trans
      (sub_eq_add_neg (left : R) (right : R)).symm)

/-- Integer casts preserve multiplication.

The four displayed sign cases reduce to natural-cast multiplication and
the ring's additive inverse laws, retaining both integer factors. -/
public theorem intCast_mul {R : Type*} [Ring R] (left right : Int) :
    ((left * right : Int) : R) = (left : R) * (right : R) := by
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right =>
          change (((left * right : Nat) : Int) : R) =
            (((left : Nat) : Int) : R) * (((right : Nat) : Int) : R)
          rw [Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
          exact NatCast.mul left right
      | negSucc right =>
          change ((Int.negOfNat (left * (right + 1)) : Int) : R) =
            (((left : Nat) : Int) : R) * ((Int.negSucc right : Int) : R)
          rw [cast_negOfNat, Int.cast_natCast, cast_negSucc,
            NatCast.mul, Multiplication.mul_neg]
  | negSucc left =>
      cases right with
      | ofNat right =>
          change ((Int.negOfNat ((left + 1) * right) : Int) : R) =
            ((Int.negSucc left : Int) : R) * (((right : Nat) : Int) : R)
          rw [cast_negOfNat, cast_negSucc, Int.cast_natCast,
            NatCast.mul, Multiplication.neg_mul]
      | negSucc right =>
          change ((((left + 1) * (right + 1) : Nat) : Int) : R) =
            ((Int.negSucc left : Int) : R) * ((Int.negSucc right : Int) : R)
          rw [Int.cast_natCast, cast_negSucc, cast_negSucc,
            NatCast.mul, Multiplication.neg_mul_neg]

/-- Integer casts preserve natural powers.

Structural induction on the retained exponent uses the ordinary integer
power recurrence and the direct multiplication cast equation. -/
public theorem intCast_pow {R : Type*} [Ring R] (value : Int) :
    ∀ exponent : Nat, ((value ^ exponent : Int) : R) = (value : R) ^ exponent
  | 0 => by
      calc
        ((Int.pow value 0 : Int) : R) = ((1 : Int) : R) :=
          congrArg (fun item : Int => (item : R)) (Arithmetic.pow_zero value)
        _ = 1 := Int.cast_one
        _ = (value : R) ^ 0 := (pow_zero _).symm
  | exponent + 1 => by
      calc
        ((Int.pow value (exponent + 1) : Int) : R) =
            ((Int.pow value exponent * value : Int) : R) :=
          congrArg (fun item : Int => (item : R)) (Arithmetic.pow_succ value exponent)
        _ = ((Int.pow value exponent : Int) : R) * (value : R) := intCast_mul _ _
        _ = (value : R) ^ exponent * (value : R) :=
          congrArg (· * (value : R)) (intCast_pow value exponent)
        _ = (value : R) ^ (exponent + 1) := (pow_succ _ _).symm

end Purelib.Algebra.Ring.IntCast
