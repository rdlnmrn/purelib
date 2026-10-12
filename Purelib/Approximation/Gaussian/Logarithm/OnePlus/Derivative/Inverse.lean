module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Factorization
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Quarter
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.OneAdd
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Inverse

/-- The finite one-plus logarithm derivative sample differs from the reciprocal by its exact geometric remainder.

The displayed Gaussian input has quadrance at most one quarter, which supplies the nonzero denominator certificate. -/
theorem log1pDerivative_sub_inverse {u :
  Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) (index : Nat) :
    Sample.log1pDerivativeSample u index - (1 + u)⁻¹ =
      -((-u) ^ (index + 1)) * (1 + u)⁻¹ := by
  have nonzero := OneAdd.one_add_ne_zero disk
  have inverseCancel : (1 + u)⁻¹ * (1 + u) = 1 := by
    simpa only [Data.Gaussian.Field.inv_eq] using
      Data.Gaussian.Field.inv_mul (1 + u) nonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne nonzero
  calc
    (Sample.log1pDerivativeSample u index - (1 + u)⁻¹) * (1 + u) =
        Sample.log1pDerivativeSample u index * (1 + u) -
          (1 + u)⁻¹ * (1 + u) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    _ = Sample.log1pDerivativeSample u index * (1 + u) - 1 := by
      rw [inverseCancel]
    _ = (1 + u) * Sample.log1pDerivativeSample u index - 1 := by
      rw [Data.Gaussian.Basic.mul_comm]
    _ = -((-u) ^ (index + 1)) := by
      rw [Factorization.log1pDerivative_geometric_remainder]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = (-((-u) ^ (index + 1)) * (1 + u)⁻¹) * (1 + u) := by
      rw [Data.Gaussian.Basic.mul_assoc, inverseCancel,
        Data.Gaussian.Basic.mul_one]

/-- The reciprocal error of the finite logarithm derivative sample is bounded by the scale-one indexed quarter-radius
allowance. -/
theorem log1pDerivative_sub_inverse_bound {u
  : Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.log1pDerivativeSample u index - (1 + u)⁻¹) ≤
      Geometric.Basic.quarterRadius 1 index := by
  rw [log1pDerivative_sub_inverse disk,
    Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_neg,
    Power.normSq_pow, Data.Gaussian.Norm.Basic.normSq_neg]
  calc
    Data.Gaussian.Norm.Basic.normSq u ^ (index + 1) * Data.Gaussian.Norm.Basic.normSq ((1 + u)⁻¹) ≤
        (1 / 4 : Fraction.Rational) ^ (index + 1) * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct
          (Data.Gaussian.Norm.Basic.normSq_nonneg u) disk (index + 1))
        (OneAdd.one_add_inverse_normSq_le_four disk)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (show 0 ≤ (1 / 4 : Fraction.Rational) ^ (index + 1) from
          Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
    _ = Geometric.Basic.quarterRadius 1 index := by
      rw [Fraction.Field.mul_comm,
        Quarter.four_mul_quarterPower_succ,
        Geometric.Basic.quarterRadius_eq_mul_pow,
        Fraction.Field.one_mul]
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Inverse

end
