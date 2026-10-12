module

public import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Embedding
import Purelib.Tactic.Ring

/-!
# Source perturbations and coefficient determinant bounds

Changing one displayed rational source adds the retained denominator times
the source displacement to its error. The same error coordinates give a
two-term quadrance bound for the original integral coefficient determinant.
-/

public section

namespace Purelib.NumberTheory.Approximation.Best.Error

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Data.GaussianInt.Pair

/-- Changing the source adds its displacement times the retained pair denominator to the original error. -/
theorem error_perturbation_identity (center sample : Gaussian.Basic.Canonical) (pair : ConvergentPair) :
    error sample pair = error center pair + (sample - center) * GaussianInt.toGaussian pair.denominator := by
  unfold error
  apply Gaussian.Basic.ext <;>
    simp only [-eq_self, -iff_self, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The coefficient determinant quadrance is bounded by the two cross products of denominator and error quadrances.

The original integral determinant equals the difference of the two
denominator-error products at every displayed source. The two-term squared
norm bound gives the inequality without dividing by either denominator.
-/
theorem coefficientIndexQuadrance_le_two_mul (source : Gaussian.Basic.Canonical) (left right : ConvergentPair) :
    (LinearCombination.coefficientIndexQuadrance left right : Fraction.Rational) ≤
      2 * ((denominatorQuadrance left : Fraction.Rational) * errorQuadrance source right +
        (denominatorQuadrance right : Fraction.Rational) * errorQuadrance source left) := by
  calc
    (LinearCombination.coefficientIndexQuadrance left right : Fraction.Rational) =
        Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (LinearCombination.coefficientDeterminant left right)) :=
      (GaussianInt.normSq_toGaussian _).symm
    _ = Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian left.denominator * error source right -
          GaussianInt.toGaussian right.denominator * error source left) :=
      congrArg Gaussian.Norm.Basic.normSq (toGaussian_coefficientDeterminant source left right)
    _ ≤ 2 * (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian left.denominator * error source right) +
        Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian right.denominator * error source left)) :=
      Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ = _ := by
      rewrite [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
        GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
      rfl

end Purelib.NumberTheory.Approximation.Best.Error
