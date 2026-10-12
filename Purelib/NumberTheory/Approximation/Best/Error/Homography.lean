module

public import Purelib.Data.GaussianInt.Pair.Matrix
public import Purelib.Geometry.Projective.Homography.Basic
public import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Approximation errors under integral homographies

The source and its numerator-denominator pair are transported by the same
matrix. Multiplication by the exact affine denominator gives an equality
between the transformed error and the original error scaled by the matrix
determinant. The denominator-coordinate identity separately retains the
source-dependent correction to the old denominator.
-/

public section

namespace Purelib.NumberTheory.Approximation.Best.Error

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2

/-- The original homographic source times its nonzero denominator is its numerator. -/
private theorem homographic_mul_denominator (matrix : Matrix GaussianInt)
    (source : Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source ≠ 0) :
    Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source *
        Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source =
      Homography.Basic.numerator (Matrix.map GaussianInt.toGaussian matrix) source := by
  unfold Homography.Basic.homographic
  rewrite [Gaussian.Basic.mul_assoc, Gaussian.Field.inv_eq,
    Gaussian.Field.inv_mul _ denominatorNonzero, Gaussian.Basic.mul_one]
  rfl

/-- Clearing the affine denominator transports the division-free error exactly.

The identity holds for every integral matrix and retained pair, provided the
displayed source avoids the matrix's affine pole. No determinant-one
assumption or normalization of the pair is required.
-/
theorem error_transform_mul_denominator (matrix : Matrix GaussianInt)
    (source : Gaussian.Basic.Canonical) (pair : ConvergentPair)
    (denominatorNonzero : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source ≠ 0) :
    error (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source)
        (pair.transform matrix) *
        Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source =
      GaussianInt.toGaussian matrix.determinant * error source pair := by
  let output := Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source
  let denominator := Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source
  have cancelled : output * denominator =
      Homography.Basic.numerator (Matrix.map GaussianInt.toGaussian matrix) source :=
    homographic_mul_denominator matrix source denominatorNonzero
  calc
    error output (pair.transform matrix) * denominator =
        (output * denominator) *
            (GaussianInt.toGaussian matrix.c * GaussianInt.toGaussian pair.numerator +
              GaussianInt.toGaussian matrix.d * GaussianInt.toGaussian pair.denominator) -
          (GaussianInt.toGaussian matrix.a * GaussianInt.toGaussian pair.numerator +
              GaussianInt.toGaussian matrix.b * GaussianInt.toGaussian pair.denominator) * denominator := by
      unfold error ConvergentPair.transform
      rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_add,
        GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul,
        GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
    _ = GaussianInt.toGaussian matrix.determinant * error source pair := by
      rewrite [cancelled]
      unfold Homography.Basic.numerator denominator Homography.Basic.denominator
        Matrix.map Matrix.determinant error
      rewrite [GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The squared transformed error obeys the same cleared determinant identity. -/
theorem errorQuadrance_transform_mul_normSq (matrix : Matrix GaussianInt)
    (source : Gaussian.Basic.Canonical) (pair : ConvergentPair)
    (denominatorNonzero : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source ≠ 0) :
    errorQuadrance (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source)
        (pair.transform matrix) *
        Gaussian.Norm.Basic.normSq
          (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source) =
      Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian matrix.determinant) * errorQuadrance source pair := by
  have norms := congrArg Gaussian.Norm.Basic.normSq
    (error_transform_mul_denominator matrix source pair denominatorNonzero)
  rewrite [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul] at norms
  exact norms

/-- Determinant-one transport retains the original squared error after paying its exact denominator factor. -/
theorem errorQuadrance_transform_of_determinant_one (matrix : Matrix GaussianInt)
    (unitDeterminant : matrix.determinant = 1) (source : Gaussian.Basic.Canonical)
    (pair : ConvergentPair)
    (denominatorNonzero : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source ≠ 0) :
    errorQuadrance (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source)
        (pair.transform matrix) *
        Gaussian.Norm.Basic.normSq
          (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source) =
      errorQuadrance source pair := by
  rewrite [errorQuadrance_transform_mul_normSq matrix source pair denominatorNonzero,
    unitDeterminant, GaussianInt.toGaussian_one, Gaussian.Norm.Basic.normSq_one]
  exact Fraction.Field.one_mul _

/-- The new integral denominator is the old denominator scaled by the source denominator, minus its error correction. -/
theorem denominator_transform (matrix : Matrix GaussianInt)
    (source : Gaussian.Basic.Canonical) (pair : ConvergentPair) :
    GaussianInt.toGaussian (pair.transform matrix).denominator =
      Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source *
          GaussianInt.toGaussian pair.denominator -
        GaussianInt.toGaussian matrix.c * error source pair := by
  unfold ConvergentPair.transform Homography.Basic.denominator Matrix.map error
  rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Determinant-one homography preserves a strict error comparison between the same two original pairs. -/
theorem errorQuadrance_lt_transform (matrix : Matrix GaussianInt)
    (unitDeterminant : matrix.determinant = 1) (source : Gaussian.Basic.Canonical)
    (lower upper : ConvergentPair)
    (denominatorNonzero : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source ≠ 0)
    (ordered : errorQuadrance source upper < errorQuadrance source lower) :
    errorQuadrance (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source)
        (upper.transform matrix) <
      errorQuadrance (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) source)
        (lower.transform matrix) := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Gaussian.Norm.Basic.normSq
      (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) source))
  · rewrite [errorQuadrance_transform_of_determinant_one matrix unitDeterminant source upper denominatorNonzero,
      errorQuadrance_transform_of_determinant_one matrix unitDeterminant source lower denominatorNonzero]
    exact ordered
  · exact Gaussian.Norm.Basic.normSq_pos denominatorNonzero

end Purelib.NumberTheory.Approximation.Best.Error
