module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Factorization
public import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sample
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Horner.Relative

open Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Factorization

/-- The next relative exponential sample minus one factors as the input times its second-relative sample. -/
theorem
  expRelSample_succ_sub_one_factor
  (z : Canonical) (index : Nat) :
    Sample.expRelSample z (index + 1) - 1 =
      z * Sample.expSecondRelSample z index := by
  rw [Sample.expRelSample, Horner.Basic.horner_succ,
    Horner.Basic.step_eq]
  rw [show (1 / ((2 : Nat) : Fraction.Rational)) = 1 / 2 by decide]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Sample.expSecondRelSample, Scale.scale_re,
      Scale.scale_im, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im, Nat.reduceAdd] <;> ring1

/-- The finite exponential linearization remainder factors as the input squared times its second-relative sample. -/
theorem
  expSample_second_order_factor (z
  : Canonical) (index : Nat) :
    Sample.sample z (index + 1) - 1 - z =
      z ^ 2 * Sample.expSecondRelSample z index := by
  calc
    Sample.sample z (index + 1) - 1 - z =
        z * Sample.expRelSample z (index + 1) - z := by
      rw [Factorization.expSample_sub_one_factor]
    _ = z * (Sample.expRelSample z (index + 1) - 1) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = z * (z * Sample.expSecondRelSample z index) := by
      rw [expRelSample_succ_sub_one_factor]
    _ = z ^ 2 * Sample.expSecondRelSample z index := by
      rw [pow_two, Data.Gaussian.Basic.mul_assoc]

/-- On the rational unit disk, the quadrance of the finite linearization remainder is at most the square of the input
quadrance. This is the explicit finite meaning of the ordinary-magnitude phrase "quadratic error". -/
theorem
  expSample_second_order_normSq_le
  {z : Canonical}
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.sample z (index + 1) - 1 - z) ≤
      Data.Gaussian.Norm.Basic.normSq z ^ 2 := by
  rw [expSample_second_order_factor,
    Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
  calc
    Data.Gaussian.Norm.Basic.normSq z ^ 2 * Data.Gaussian.Norm.Basic.normSq (Sample.expSecondRelSample
      z index) ≤
        Data.Gaussian.Norm.Basic.normSq z ^ 2 * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Sample.expSecondRelSample_bounded unitInput index)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg z) 2)
    _ = Data.Gaussian.Norm.Basic.normSq z ^ 2 :=
      Fraction.Field.mul_one_direct _
end Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Factorization

end
