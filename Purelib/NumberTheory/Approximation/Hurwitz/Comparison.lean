module
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.GaussianInt.Pair.Basis
public import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Encoding
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data

open Purelib.NumberTheory.Approximation

@[expose] public section

/-!
# Finite approximation algebra for Hurwitz convergents

This module isolates the calculation underlying a second-kind approximation
comparison.  The error of `p/q` is represented without division as `qz-p`.
Adjacent finite continuants have determinant `1` or `-1`, so every displayed
Gaussian-integer competitor has explicit coefficients in that adjacent
continuant basis.  No enumeration of Gaussian rationals is used.
-/

namespace Purelib.NumberTheory.Approximation.Hurwitz.Comparison

/-- Prepending the same Gaussian integer digit to two continuants negates their pair determinant. -/
theorem determinant_prepend (digit : GaussianInt)
    (left right : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.Pair.Basis.determinant (Data.ComplexContinuedFraction.Hurwitz.Continuant.prepend digit left)
      (Data.ComplexContinuedFraction.Hurwitz.Continuant.prepend digit right) =
      -GaussianInt.Pair.Basis.determinant left right := by
  apply GaussianInt.ext <;>
    simp only [GaussianInt.Pair.Basis.determinant, Data.ComplexContinuedFraction.Hurwitz.Continuant.prepend,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Every pair of adjacent finite continuants has determinant `1` or `-1`.
The proof follows the displayed digit list and merely flips the sign at each
front digit. -/
theorem adjacent_hasUnitDeterminant (initialDigits : List
  GaussianInt)
    (nextDigit : GaussianInt) :
    GaussianInt.Pair.Basis.HasUnitDeterminant
      (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant (initialDigits ++ [nextDigit]))
      (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant initialDigits) := by
  induction initialDigits with
  | nil =>
      right
      apply GaussianInt.ext <;>
        simp only [List.nil_append, GaussianInt.Pair.Basis.determinant,
          Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant,
          Data.ComplexContinuedFraction.Hurwitz.Continuant.prepend,
          GaussianInt.add_re,
          GaussianInt.add_im,
          GaussianInt.sub_re,
          GaussianInt.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im,
          GaussianInt.zero_re,
          GaussianInt.zero_im,
          GaussianInt.one_re,
          GaussianInt.one_im] <;>
        ring1
  | cons head tail inductionHypothesis =>
      rw [List.cons_append, Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant_cons,
        Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant_cons,
        GaussianInt.Pair.Basis.HasUnitDeterminant, determinant_prepend]
      rcases inductionHypothesis with positive | negative
      · right
        rw [positive]
      · left
        rw [negative]
        exact neg_neg 1

/-- The first Hurwitz convergent has exactly the nearest-division residual as its division-free error. -/
theorem firstConvergent_error (fraction :
  GaussianInt.Fraction) :
    Best.Error.error fraction.value (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
      [GaussianInt.Division.Nearest.digit fraction]) =
      GaussianInt.Division.Nearest.residual fraction := by
  simp only [Best.Error.error, Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant,
    Data.ComplexContinuedFraction.Hurwitz.Continuant.prepend,
    GaussianInt.mul_one,
    GaussianInt.add_zero, GaussianInt.toGaussian_one,
    Gaussian.Basic.mul_one,
    GaussianInt.Division.Nearest.residual, GaussianInt.Division.Nearest.digit,
    GaussianInt.Nearest.remainder, -eq_self, -iff_self]
  rfl

/-- The first Hurwitz convergent is already second-kind optimal against every
displayed Gaussian integer. -/
theorem firstConvergent_atLeastAsGoodAs_integral
    (fraction : GaussianInt.Fraction) (competitor : GaussianInt) :
    Best.Error.AtLeastAsGoodAs fraction.value
      (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant [GaussianInt.Division.Nearest.digit fraction])
      (GaussianInt.Pair.Basis.integralPair competitor) := by
  rw [Best.Error.AtLeastAsGoodAs, firstConvergent_error]
  simpa only [GaussianInt.Division.Nearest.residual, Best.Error.error, GaussianInt.Pair.Basis.integralPair,
    GaussianInt.toGaussian_one, Gaussian.Basic.mul_one]
    using GaussianInt.Nearest.remainder_normSq_le_competitor
      fraction.value competitor

/-- The complete finite encoding reconstructs its displayed source, hence
has zero division-free error. -/
theorem encodedConvergent_error_eq_zero (fraction :
  GaussianInt.Fraction) :
    Best.Error.error fraction.value (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
      (Data.ComplexContinuedFraction.Hurwitz.Encoding.encode fraction)) = 0 := by
  rw [Best.Error.error, Data.ComplexContinuedFraction.Hurwitz.Encoding.encode_reconstruct fraction]
  exact Gaussian.Basic.sub_self _

/-- The complete finite Hurwitz convergent is at least as good as every displayed competitor.

Its division-free error is zero because the finite encoding reconstructs the retained rational source; every competitor
has nonnegative error quadrance. -/
theorem encodedConvergent_atLeastAsGoodAs (fraction :
  GaussianInt.Fraction)
    (competitor : GaussianInt.Pair.Basic.ConvergentPair) :
    Best.Error.AtLeastAsGoodAs fraction.value (Data.ComplexContinuedFraction.Hurwitz.Continuant.continuant
      (Data.ComplexContinuedFraction.Hurwitz.Encoding.encode fraction)) competitor := by
  rw [Best.Error.AtLeastAsGoodAs, encodedConvergent_error_eq_zero, Gaussian.Norm.Basic.normSq_zero]
  exact Gaussian.Norm.Basic.normSq_nonneg _

end Purelib.NumberTheory.Approximation.Hurwitz.Comparison

end
