module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Factorization
public import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sample
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Factorization
public import Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Exponential.Horner.Addition

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

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Differential

/-! ## Differential law for the executable exponential -/

/-- The finite secant factor for translating the exponential computation by `increment`. On its diagonal (`increment =
0`) it is the displayed exponential sample itself. -/
def expDifferentialSample (base increment :
  Canonical) (index : Nat) : Canonical :=
  Sample.sample base index * Sample.expRelSample increment index

/-- At zero increment, the finite exponential secant factor equals the original base exponential sample. -/
theorem expDifferentialSample_diagonal (base :
  Canonical) (index : Nat) :
    expDifferentialSample base 0 index =
      Sample.sample base index := by
  rw [expDifferentialSample, Sample.expRelSample_zero,
    Data.Gaussian.Basic.mul_one]

/-- The product computation of `exp(base) * exp(increment)` has an exact finite first-order factorization at every
sample depth. -/
theorem expProductSample_sub_base_factor (base
  increment : Canonical)
    (index : Nat) :
    Sequence.expProductSample base increment index -
        Sample.sample base index =
      increment * expDifferentialSample base increment index :=
        by
  rw [Sequence.expProductSample,
    expDifferentialSample]
  calc
    Sample.sample base index *
          Sample.sample increment index -
        Sample.sample base index =
      Sample.sample base index *
        (Sample.sample increment index - 1) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = Sample.sample base index *
        (increment * Sample.expRelSample increment index) := by
      rw [Factorization.expSample_sub_one_factor]
    _ = increment *
        (Sample.sample base index *
          Sample.expRelSample increment index) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im] <;> ring1

/-- After subtracting its diagonal factor, the translated exponential computation has an exact quadratic remainder at
each positive displayed depth. -/
theorem expProductSample_second_order (base
  increment : Canonical)
    (index : Nat) :
    Sequence.expProductSample base increment
          (index + 1) -
        Sample.sample base (index + 1) -
        increment * Sample.sample base (index + 1) =
      increment ^ 2 *
        (Sample.sample base (index + 1) *
          Sample.expSecondRelSample increment index) := by
  rw [Sequence.expProductSample]
  calc
    Sample.sample base (index + 1) *
          Sample.sample increment (index + 1) -
        Sample.sample base (index + 1) -
        increment * Sample.sample base (index + 1) =
      Sample.sample base (index + 1) *
        (Sample.sample increment (index + 1) - 1 -
          increment) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = Sample.sample base (index + 1) *
        (increment ^ 2 * Sample.expSecondRelSample increment index) := by
      rw [Factorization.expSample_second_order_factor]
    _ = increment ^ 2 *
        (Sample.sample base (index + 1) *
          Sample.expSecondRelSample increment index) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im, pow_two] <;> ring1

/-- The translated product program has a uniform, wholly rational quadratic quadrance bound on the two displayed unit
disks. -/
theorem expProductSample_second_order_normSq_le
  {base increment : Canonical}
    (baseUnit : Data.Gaussian.Norm.Basic.normSq base ≤ 1) (incrementUnit :
      Data.Gaussian.Norm.Basic.normSq increment ≤ 1)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (Sequence.expProductSample base increment
              (index + 1) -
            Sample.sample base (index + 1) -
            increment * Sample.sample base (index + 1)) ≤
      10 * Data.Gaussian.Norm.Basic.normSq increment ^ 2 := by
  rw [expProductSample_second_order,
    Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow, Data.Gaussian.Norm.Basic.normSq_mul]
  have cofactorBound :
      Data.Gaussian.Norm.Basic.normSq (Sample.sample base (index + 1)) *
          Data.Gaussian.Norm.Basic.normSq (Sample.expSecondRelSample increment index) ≤ 10 := by
    calc
      Data.Gaussian.Norm.Basic.normSq (Sample.sample base (index + 1)) *
            Data.Gaussian.Norm.Basic.normSq (Sample.expSecondRelSample increment index) ≤ 10 * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_direct
          (Sample.sample_bounded base baseUnit (index + 1))
          (Sample.expSecondRelSample_bounded incrementUnit index)
          (Data.Gaussian.Norm.Basic.normSq_nonneg (Sample.expSecondRelSample increment index)) (by decide)
      _ = 10 := Fraction.Field.mul_one_direct _
  calc
    Data.Gaussian.Norm.Basic.normSq increment ^ 2 *
          (Data.Gaussian.Norm.Basic.normSq (Sample.sample base (index + 1)) *
            Data.Gaussian.Norm.Basic.normSq (Sample.expSecondRelSample increment index)) ≤
        Data.Gaussian.Norm.Basic.normSq increment ^ 2 * 10 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct cofactorBound
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          (Data.Gaussian.Norm.Basic.normSq_nonneg increment) 2)
    _ = 10 * Data.Gaussian.Norm.Basic.normSq increment ^ 2 :=
      Fraction.Field.mul_comm _ _
end Purelib.Approximation.Gaussian.Exponential.Horner.Differential

end
