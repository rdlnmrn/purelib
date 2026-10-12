module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Basic
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Local

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Rat

/-- Compute the canonical Gaussian square of a reduced logarithm argument.

The original Gaussian product supplies the canonical square without choosing a
new argument or logarithm branch. -/
@[expose] def squaredArgument (z : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  Data.Gaussian.Basic.canonical (z * z)

/-- The canonical reduced squared argument equals the original argument multiplied by itself. -/
theorem squaredArgument_eq (z : Data.Gaussian.Basic.Canonical) : squaredArgument z = z * z :=
  Data.Gaussian.Basic.canonical_eq _

/-- Squaring preserves the one-ninth quadrance disk for the reduced logarithm argument. -/
theorem squaredArgument_bound {z : Data.Gaussian.Basic.Canonical} (zBound : Data.Gaussian.Norm.Basic.normSq z ≤
  1 / 9) :
    Data.Gaussian.Norm.Basic.normSq (squaredArgument z) ≤ 1 / 9 := by
  rw [squaredArgument_eq, Data.Gaussian.Norm.Basic.normSq_mul]
  calc
    Data.Gaussian.Norm.Basic.normSq z * Data.Gaussian.Norm.Basic.normSq z ≤ (1 / 9 :
      Fraction.Rational) * (1 / 9) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct zBound zBound
        (Data.Gaussian.Norm.Basic.normSq_nonneg z) (by decide)
    _ ≤ 1 / 9 := by decide

/-- Compute twice the displayed reduced Gaussian argument.

The original rational scalar two multiplies the same Gaussian argument before
canonical readback. -/
@[expose] def outputFactor (z : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  Data.Gaussian.Basic.canonical (ComplexLog.scalar 2 * z)

/-- The canonical output factor equals the rational scalar two times the original reduced argument. -/
theorem outputFactor_eq (z : Data.Gaussian.Basic.Canonical) : outputFactor z = ComplexLog.scalar 2 * z :=
  Data.Gaussian.Basic.canonical_eq _

/-- A reduced argument with quadrance at most one ninth gives an output factor with quadrance at most one. -/
theorem outputFactor_bound {z : Data.Gaussian.Basic.Canonical} (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1
  / 9) :
    Data.Gaussian.Norm.Basic.normSq (outputFactor z) ≤ 1 := by
  rw [outputFactor_eq, Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
  calc
    (2 : Fraction.Rational) ^ 2 * Data.Gaussian.Norm.Basic.normSq z ≤ 4 * (1 / 9 : Fraction.Rational) := by
      rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct zBound
        (by decide)
    _ ≤ 1 := by decide

/-- The output factor's quadrance is at most four ninths on the displayed reduced disk. -/
theorem outputFactor_bound_four_ninth {z : Data.Gaussian.Basic.Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) :
    Data.Gaussian.Norm.Basic.normSq (outputFactor z) ≤ 4 / 9 := by
  rw [outputFactor_eq, Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
  calc
    (2 : Fraction.Rational) ^ 2 * Data.Gaussian.Norm.Basic.normSq z ≤ 4 * (1 / 9 : Fraction.Rational) := by
      rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct zBound
        (by decide)
    _ = 4 / 9 := by decide

/-- Compute the canonical finite Gaussian logarithm Horner sample.

It multiplies twice the original reduced argument by the retained finite Horner value at its squared argument and
starting coefficient index one. -/
@[expose] def sample (z : Data.Gaussian.Basic.Canonical) (depth : Nat) : Data.Gaussian.Basic.Canonical :=
  Data.Gaussian.Basic.canonical (outputFactor z * Horner.Basic.horner (squaredArgument z) 1 depth)

/-- The canonical logarithm sample equals its output factor times the displayed finite Horner value. -/
theorem sample_eq (z : Data.Gaussian.Basic.Canonical) (depth : Nat) :
    sample z depth = outputFactor z * Horner.Basic.horner (squaredArgument z) 1 depth :=
  Data.Gaussian.Basic.canonical_eq _

/-- Every finite logarithm sample on the one-ninth reduced disk has squared norm at most four. -/
theorem sample_bounded {z : Data.Gaussian.Basic.Canonical} (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9)
    (depth : Nat) : Data.Gaussian.Norm.Basic.normSq (sample z depth) ≤ 4 := by
  rw [sample_eq, Data.Gaussian.Norm.Basic.normSq_mul]
  calc
    Data.Gaussian.Norm.Basic.normSq (outputFactor z) *
        Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner (squaredArgument z) 1 depth) ≤ 1 * 4 :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (outputFactor_bound zBound)
        (Horner.Bounds.horner_bound (squaredArgument_bound zBound) depth 1 (by decide))
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1) (by decide)).le
    _ = 4 := Fraction.Field.one_mul _

/-- Sharper bound: every displayed local complex-log truncation lies in the closed unit disk. -/
theorem sample_bounded_one {z : Data.Gaussian.Basic.Canonical} (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1
  / 9)
    (depth : Nat) : Data.Gaussian.Norm.Basic.normSq (sample z depth) ≤ 1 := by
  rw [sample_eq, Data.Gaussian.Norm.Basic.normSq_mul]
  calc
    Data.Gaussian.Norm.Basic.normSq (outputFactor z) *
        Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner (squaredArgument z) 1 depth) ≤
      (4 / 9 : Fraction.Rational) * (9 / 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_direct
          (outputFactor_bound_four_ninth zBound)
          (Horner.Bounds.horner_bound_nine_four (squaredArgument_bound zBound)
            depth 1 (by decide))
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
    _ = 1 := by decide

/-- Later logarithm Horner samples obey the earlier quarter-power bound.

The retained index ordering supplies its exact natural difference. Factoring the
same finite Horner readings bounds their squared distance by five times the
earlier quarter-power. -/
theorem sample_later_close {z : Data.Gaussian.Basic.Canonical} (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1
  / 9)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Norm.Basic.normSq (sample z later - sample z earlier) ≤
      5 * (1 / 4 : Fraction.Rational) ^ earlier := by
  let extra := later - earlier
  have laterRead : later = earlier + extra :=
    (Data.Nat.Subtraction.add_sub_of_le order).symm
  rw [laterRead]
  rw [sample_eq, sample_eq]
  have identity :
      outputFactor z * Horner.Basic.horner (squaredArgument z) 1 (earlier + extra) -
          outputFactor z * Horner.Basic.horner (squaredArgument z) 1 earlier =
        outputFactor z *
          (Horner.Basic.horner (squaredArgument z) 1 (earlier + extra) -
            Horner.Basic.horner (squaredArgument z) 1 earlier) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
  rw [identity, Data.Gaussian.Norm.Basic.normSq_mul]
  calc
    Data.Gaussian.Norm.Basic.normSq (outputFactor z) *
        Data.Gaussian.Norm.Basic.normSq
          (Horner.Basic.horner (squaredArgument z) 1 (earlier + extra) -
            Horner.Basic.horner (squaredArgument z) 1 earlier) ≤
        (4 / 9 : Fraction.Rational) *
          (10 * (1 / 4 : Fraction.Rational) ^ earlier) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_direct
      · rw [outputFactor_eq, Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
        calc
          (2 : Fraction.Rational) ^ 2 * Data.Gaussian.Norm.Basic.normSq z ≤ 4 * (1 / 9 : Fraction.Rational) :=
            by
            rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
            exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              zBound (by decide)
          _ = 4 / 9 := by decide
      · exact Horner.Bounds.horner_add_depth_close (squaredArgument_bound zBound)
          earlier extra 1 (by decide)
      · exact Data.Gaussian.Norm.Basic.normSq_nonneg _
      · decide
    _ ≤ 5 * (1 / 4 : Fraction.Rational) ^ earlier := by
      have powerNonnegative :
          0 ≤ (1 / 4 : Fraction.Rational) ^ earlier :=
        Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) earlier
      calc
        (4 / 9 : Fraction.Rational) *
            (10 * (1 / 4 : Fraction.Rational) ^ earlier) =
            (40 / 9 : Fraction.Rational) * (1 / 4 : Fraction.Rational) ^ earlier := by
          calc
            (4 / 9 : Fraction.Rational) *
                (10 * (1 / 4 : Fraction.Rational) ^ earlier) =
                ((4 / 9 : Fraction.Rational) * 10) *
                  (1 / 4 : Fraction.Rational) ^ earlier := by
              rw [Fraction.Field.mul_assoc]
            _ = (40 / 9 : Fraction.Rational) *
                  (1 / 4 : Fraction.Rational) ^ earlier := by
              rw [show (4 / 9 : Fraction.Rational) * 10 = 40 / 9 by
                rw [Fraction.Field.div_eq_mul_inv_direct,
                  Fraction.Field.div_eq_mul_inv_direct]
                ring1]
        _ ≤ 5 * (1 / 4 : Fraction.Rational) ^ earlier :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by
              apply (Fraction.Order.Field.div_le_iff_pos
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 9) (by decide))).2
              calc
                (40 : Fraction.Rational) ≤ 45 :=
                  Fraction.Cast.Order.natCast_le_direct (by decide)
                _ = 5 * 9 := by ring1)
            powerNonnegative
end Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample

end
