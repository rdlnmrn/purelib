module
import Purelib.Data.Gaussian.Basic

import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.GroupWithZero.NeZero

section
@[expose] public section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

namespace Purelib.Data.Gaussian.Power

open Purelib.Data.Gaussian in
/-- Gaussian conjugation commutes with each natural power. -/
theorem conj_pow (point : Basic.Canonical) : ∀ degree,
    Basic.conj (point ^ degree) = Basic.conj point ^ degree
  | 0 => rfl
  | degree + 1 => by
      rw [pow_succ, pow_succ, Basic.conj_mul, conj_pow point degree]
end Purelib.Data.Gaussian.Power

end

section
@[expose] public section

/-!
# Gaussian rationals

The public `Purelib.Data.Gaussian` family denotes the quotient-free structural
pair from `Gaussian.Canonical`.  The operations below provide its default
calculation API.
-/

namespace Purelib.Data
namespace Gaussian

open Purelib.Data.Gaussian
/-- Compute a Gaussian natural power by repeated right multiplication, starting at one. -/
def Power.natPow (source : Basic.Canonical) : Nat → Basic.Canonical
  | 0 => 1
  | exponent + 1 => Power.natPow source exponent * source

/-- The recursive Gaussian power at exponent zero is one. -/
@[simp] theorem Power.natPow_zero (source : Basic.Canonical) : Power.natPow source 0 = 1 :=
  rfl

/-- The successor recursive Gaussian power multiplies the previous power by the original Gaussian. -/
@[simp] theorem Power.natPow_succ (source : Basic.Canonical) (exponent : Nat) :
    Power.natPow source (exponent + 1) = Power.natPow source exponent * source := rfl

/-- The squared norm of the recursive Gaussian power is the corresponding rational power of its squared norm. -/
theorem Power.normSq_natPow (source : Basic.Canonical) (exponent : Nat) :
    Norm.Basic.normSq (Power.natPow source exponent) = Norm.Basic.normSq source ^ exponent := by
  induction exponent with
  | zero => exact Norm.Basic.normSq_one
  | succ exponent inductionHypothesis =>
      rw [Power.natPow_succ, Norm.Basic.normSq_mul, inductionHypothesis, pow_succ]

/-- Every recursive natural power of a nonzero Gaussian is nonzero. -/
theorem Power.natPow_ne_zero_direct (source : Basic.Canonical) (nonzero : source ≠ 0) :
    ∀ exponent : Nat, Power.natPow source exponent ≠ 0
  | 0 => one_ne_zero
  | exponent + 1 =>
      Field.mul_ne_zero_direct (Power.natPow_ne_zero_direct source nonzero exponent) nonzero

/-- Taking squared norm commutes with canonical Gaussian natural powers. -/
theorem Power.normSq_pow (source : Basic.Canonical) (exponent : Nat) :
    Norm.Basic.normSq (source ^ exponent) = Norm.Basic.normSq source ^ exponent := by
  induction exponent with
  | zero => exact Norm.Basic.normSq_one
  | succ exponent inductionHypothesis =>
      rw [pow_succ, Norm.Basic.normSq_mul, inductionHypothesis, pow_succ]

/-- Every canonical natural power of a nonzero Gaussian remains nonzero. -/
theorem Power.pow_ne_zero_direct (source : Basic.Canonical) (nonzero : source ≠ 0) :
    ∀ exponent : Nat, source ^ exponent ≠ 0
  | 0 => one_ne_zero
  | exponent + 1 => by
      rw [pow_succ]
      exact Field.mul_ne_zero_direct (Power.pow_ne_zero_direct source nonzero exponent)
        nonzero

end Gaussian

end Purelib.Data

end

end

section
@[expose] public section

/-!
# Parity-aware finite square-factor reduction

An exact multiplicity basis gives `p = s * s * q`: half of each
multiplicity goes into `s`, and only odd multiplicities remain in `q`.
The scalar stays in `q`, without extracting a square root in the coefficient
field.  This is not the squarefree radical, which would retain even factors.
-/

namespace Purelib.Polynomial.SquareFactorReduction

end Purelib.Polynomial.SquareFactorReduction

section
namespace Purelib.Data.Gaussian.Power

open _root_.Purelib.Polynomial.SquareFactorReduction
open Purelib.Data.Gaussian
/-- A Gaussian power at the sum of two natural exponents is the product of the two powers.

Natural induction splits the original power operation without changing its Gaussian multiplication or either exponent.
-/
private theorem powerAdd (value : Basic.Canonical) (left right
  : Nat) :
    value ^ (left + right) = value ^ left * value ^ right := by
  induction right with
  | zero =>
      simp only [Nat.add_zero, pow_zero, mul_one, -eq_self, -iff_self]
      rfl
  | succ right ih =>
      rw [Nat.add_succ, pow_succ, ih, pow_succ]
      exact _root_.mul_assoc _ _ _
/-- Split a Gaussian power into two equal half-exponent powers and its retained parity factor. -/
private theorem powerParity (value : Basic.Canonical)
  (exponent : Nat) :
    value ^ exponent = value ^ (exponent / 2) * value ^ (exponent / 2) *
      (if exponent % 2 = 0 then 1 else value) := by
  have balance : exponent = exponent / 2 + exponent / 2 + exponent % 2 := by omega
  calc
    value ^ exponent = value ^ (exponent / 2 + exponent / 2 + exponent % 2) :=
      congrArg (fun n => value ^ n) balance
    _ = value ^ (exponent / 2) * value ^ (exponent / 2) * value ^ (exponent % 2) := by
      rw [powerAdd, powerAdd]
    _ = _ := by
      by_cases even : exponent % 2 = 0
      · rw [if_pos even, even, pow_zero]
      · have odd : exponent % 2 = 1 := by omega
        rw [if_neg even, odd, pow_one]
end Purelib.Data.Gaussian.Power
end

namespace Purelib.Polynomial.SquareFactorReduction

end Purelib.Polynomial.SquareFactorReduction

end
