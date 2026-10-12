module
import Purelib.Algebra.NatCast
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative.Sample
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Bounds
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum

open Purelib.Approximation.Gaussian.Logarithm.OnePlus

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.Relative

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative

open Purelib.Data.Gaussian

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

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Factorization

/-- The next relative-logarithm term factors as the input times the matching second-relative term. -/
theorem log1pRelTerm_succ_factor (u
  : Data.Gaussian.Basic.Canonical) (index : Nat) :
    Sample.log1pRelTerm u (index + 1) =
      u * Sample.log1pSecondRelTerm u index := by
  rw [Sample.log1pRelTerm, Sample.log1pSecondRelTerm, pow_succ]
  rw [show index + 1 + 1 = index + 2 by ring1]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re,
      Scale.scale_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im,
      NatCast.add] <;> ring1

/-- Subtracting one from the next relative-logarithm sample leaves the input times the second-relative sample. -/
theorem
  log1pRelSample_succ_sub_one_factor
  (u : Data.Gaussian.Basic.Canonical) (index : Nat) :
    Sample.log1pRelSample u (index + 1) - 1 =
      u * Sample.log1pSecondRelSample u index := by
  rw [Sample.log1pRelSample,
    Prefix.sum_succ_front,
    Sample.log1pRelTerm_zero]
  calc
    1 + Prefix.sum
          (fun termIndex => Sample.log1pRelTerm u (termIndex + 1)) (index + 1) - 1 =
        Prefix.sum
          (fun termIndex => Sample.log1pRelTerm u (termIndex + 1)) (index + 1) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = Prefix.sum
        (fun termIndex => u * Sample.log1pSecondRelTerm u termIndex) (index + 1) :=
      Prefix.sum_congr
        (fun termIndex => Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Factorization.log1pRelTerm_succ_factor
          u termIndex) (index + 1)
    _ = u * Sample.log1pSecondRelSample u index := by
      exact (Prefix.mul_sum_left
        u (Sample.log1pSecondRelTerm u) (index + 1)).symm

/-- The finite logarithm linearization remainder factors as the squared input times its second-relative sample. -/
theorem
  log1pSample_second_order_factor
  (u : Data.Gaussian.Basic.Canonical) (index : Nat) :
    Sample.log1pSample u (index + 1) - u =
      u ^ 2 * Sample.log1pSecondRelSample u index := by
  rw [Sample.log1pSample]
  calc
    u * Sample.log1pRelSample u (index + 1) - u =
        u * (Sample.log1pRelSample u (index + 1) - 1) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = u * (u * Sample.log1pSecondRelSample u index) := by
      rw [Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Factorization.log1pRelSample_succ_sub_one_factor]
    _ = u ^ 2 * Sample.log1pSecondRelSample u index := by
      rw [pow_two, Data.Gaussian.Basic.mul_assoc]

/-- On the certified quarter disk, the quadrance of the finite local-log linearization remainder is bounded by four
times the square of the input quadrance. -/
theorem
  log1pSample_second_order_normSq_le
  {u : Data.Gaussian.Basic.Canonical}
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.log1pSample u (index + 1) - u) ≤
      4 * Data.Gaussian.Norm.Basic.normSq u ^ 2 := by
  rw [Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Factorization.log1pSample_second_order_factor,
    Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
  calc
    Data.Gaussian.Norm.Basic.normSq u ^ 2 * Data.Gaussian.Norm.Basic.normSq
      (Sample.log1pSecondRelSample u index) ≤
        Data.Gaussian.Norm.Basic.normSq u ^ 2 * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (SecondRelative.Bounds.log1pSecondRelSample_bounded disk index)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg u) 2)
    _ = 4 * Data.Gaussian.Norm.Basic.normSq u ^ 2 :=
      Fraction.Field.mul_comm _ _
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Factorization

end
