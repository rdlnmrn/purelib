module
public import Mathlib.Tactic.NormNum.Result

public import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Semiring.Normalization

namespace Purelib.Algebra.Ring.Normalization

open Purelib.Algebra

-- Read the retained ring fields directly instead of rebuilding this shortcut.
attribute [local instance high] SubNegMonoid.toNeg

variable {R : Type*} [CommRing R]

/-- A displayed additive inverse is the negation of the other summand. -/
private theorem neg_eq_of_sum_zero {left right : R} (vanishes : left + right = 0) :
    -left = right := by
  calc
    -left = -left + 0 :=
      (Semiring.Normalization.add_pf_add_zero (-left)).symm
    _ = -left + (left + right) := congrArg (-left + ·) vanishes.symm
    _ = (-left + left) + right := (add_assoc _ _ _).symm
    _ = 0 + right := congrArg (· + right) (AddGroup.neg_add_cancel left)
    _ = right := Semiring.Normalization.add_pf_zero_add _

/-- The negation of the zero normalized value is zero. -/
public theorem neg_zero : -(0 : R) = 0 :=
  neg_eq_of_sum_zero (Semiring.Normalization.add_pf_zero_add 0)

/-- Computed negations determine the negation of a sum. -/
public theorem neg_add {a₁ a₂ b₁ b₂ : R} (first : -a₁ = b₁) (second : -a₂ = b₂) :
    -(a₁ + a₂) = b₁ + b₂ := by
  have firstCancels : a₁ + b₁ = 0 := by
    rw [← first, add_comm]
    exact AddGroup.neg_add_cancel a₁
  have secondCancels : a₂ + b₂ = 0 := by
    rw [← second, add_comm]
    exact AddGroup.neg_add_cancel a₂
  have combined := Semiring.Normalization.add_pf_add_overlap firstCancels secondCancels
  rw [Semiring.Normalization.add_pf_zero_add] at combined
  exact neg_eq_of_sum_zero combined

/-- A computed coefficient negation determines the negation of a monomial. -/
public theorem neg_mul (a₁ : R) (a₂ : Nat) {a₃ b : R} (computed : -a₃ = b) :
    -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b := by
  apply neg_eq_of_sum_zero
  rw [← mul_add, ← computed, add_comm a₃ (-a₃), AddGroup.neg_add_cancel,
    mul_zero]

/-- A computed negation and sum determine a subtraction. -/
public theorem sub_pf {a b c d : R} (negative : -b = c) (computed : a + c = d) :
    a - b = d := by
  rw [SubNegMonoid.sub_eq_add_neg, negative]
  exact computed

/-- Scalar equality transports a computed negation. -/
public theorem neg_congr {a a' b : R} (source : a = a') (computed : -a' = b) :
    -a = b := (congrArg Neg.neg source).trans computed

/-- A negative integer certificate gives its retained normalized coefficient.

The input certificate supplies the displayed negative value. Appending the
ring's additive zero preserves that exact integer cast and computed coefficient.
-/
public theorem cast_neg {n : Nat} {R : Type*} [Ring R] {a : R}
    (computed : Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n)) :
    a = (Int.negOfNat n).rawCast + 0 :=
  computed.out.trans (AddZeroClass.add_zero _).symm

end Purelib.Algebra.Ring.Normalization
