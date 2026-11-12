module

public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Quadrance of paired sums and conjugate phase rotations

The sum and difference retain their original two inputs. Multiplication by
one phase and its actual conjugate preserves their paired quadrance, giving
a sharper half-sum bound than independent estimates of the rotated terms.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Parallelogram

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- The sum and difference of two original Gaussian values have twice their total quadrance. -/
theorem sum_difference (first last : Canonical) :
    Norm.Basic.normSq (first + last) + Norm.Basic.normSq (first - last) =
      2 * (Norm.Basic.normSq first + Norm.Basic.normSq last) := by
  change ((first.re + last.re) ^ 2 + (first.im + last.im) ^ 2) +
    ((first.re - last.re) ^ 2 + (first.im - last.im) ^ 2) =
      2 * ((first.re ^ 2 + first.im ^ 2) + (last.re ^ 2 + last.im ^ 2))
  ring1

/-- The original half-sum and half-difference share one half of the total input quadrance. -/
theorem half_sum_difference (first last : Canonical) :
    Norm.Basic.normSq ((1 / 2 : Canonical) * (first + last)) +
      Norm.Basic.normSq ((1 / 2 : Canonical) * (first - last)) =
        (1 / 2 : Fraction.Rational) * (Norm.Basic.normSq first + Norm.Basic.normSq last) := by
  have half : Norm.Basic.normSq (1 / 2 : Canonical) = (1 / 4 : Fraction.Rational) := by decide +kernel
  calc
    _ = (1 / 4 : Fraction.Rational) *
        (Norm.Basic.normSq (first + last) + Norm.Basic.normSq (first - last)) := by
      rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, half]
      ring1
    _ = (1 / 4 : Fraction.Rational) * (2 * (Norm.Basic.normSq first + Norm.Basic.normSq last)) :=
      congrArg (fun value : Fraction.Rational => (1 / 4) * value) (sum_difference first last)
    _ = ((1 / 4 : Fraction.Rational) * 2) * (Norm.Basic.normSq first + Norm.Basic.normSq last) := by ring1
    _ = _ := congrArg (fun value : Fraction.Rational => value *
      (Norm.Basic.normSq first + Norm.Basic.normSq last))
      (by decide +kernel : (1 / 4 : Fraction.Rational) * 2 = 1 / 2)

/-- A phase and its actual conjugate preserve the total quadrance of the paired half-sum and half-difference.

Both rotated expressions use the same original inputs and phase. The
identity holds before imposing unit quadrance on that phase; independent
phase choices would not supply this paired formula.
-/
theorem rotated_half_sum_difference (first last phase : Canonical) :
    Norm.Basic.normSq ((1 / 2 : Canonical) *
        ((first + last) * phase + (first - last) * Gaussian.Basic.conj phase)) +
      Norm.Basic.normSq ((1 / 2 : Canonical) *
        ((first + last) * phase - (first - last) * Gaussian.Basic.conj phase)) =
      (Norm.Basic.normSq first + Norm.Basic.normSq last) * Norm.Basic.normSq phase := by
  calc
    _ = (1 / 2 : Fraction.Rational) *
        (Norm.Basic.normSq ((first + last) * phase) +
          Norm.Basic.normSq ((first - last) * Gaussian.Basic.conj phase)) :=
      half_sum_difference ((first + last) * phase) ((first - last) * Gaussian.Basic.conj phase)
    _ = (1 / 2 : Fraction.Rational) *
        ((Norm.Basic.normSq (first + last) + Norm.Basic.normSq (first - last)) * Norm.Basic.normSq phase) := by
      rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Norm.Basic.normSq_conj]
      ring1
    _ = (1 / 2 : Fraction.Rational) *
        ((2 * (Norm.Basic.normSq first + Norm.Basic.normSq last)) * Norm.Basic.normSq phase) :=
      congrArg (fun value : Fraction.Rational => (1 / 2) * (value * Norm.Basic.normSq phase))
        (sum_difference first last)
    _ = ((1 / 2 : Fraction.Rational) * 2) *
        ((Norm.Basic.normSq first + Norm.Basic.normSq last) * Norm.Basic.normSq phase) := by ring1
    _ = _ := (congrArg (fun value : Fraction.Rational => value *
      ((Norm.Basic.normSq first + Norm.Basic.normSq last) * Norm.Basic.normSq phase))
      (by decide +kernel : (1 / 2 : Fraction.Rational) * 2 = 1)).trans (Fraction.Field.one_mul _)

/-- A unit phase bounds its paired rotated half-sum by the total quadrance of the two original inputs. -/
theorem rotated_half_sum_le (first last phase : Canonical) (unit : Norm.Basic.normSq phase = 1) :
    Norm.Basic.normSq ((1 / 2 : Canonical) *
      ((first + last) * phase + (first - last) * Gaussian.Basic.conj phase)) ≤
      Norm.Basic.normSq first + Norm.Basic.normSq last := by
  have total := rotated_half_sum_difference first last phase
  rewrite [unit, Fraction.Field.mul_one_direct] at total
  have bound := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (Norm.Basic.normSq ((1 / 2 : Canonical) *
      ((first + last) * phase + (first - last) * Gaussian.Basic.conj phase))))
    (Norm.Basic.normSq_nonneg ((1 / 2 : Canonical) *
      ((first + last) * phase - (first - last) * Gaussian.Basic.conj phase)))
  have scalar (value : Fraction.Rational) : value = value + 0 := by ring1
  exact (scalar _).trans_le (bound.trans_eq total)

end Purelib.Data.Gaussian.Norm.Parallelogram

end
