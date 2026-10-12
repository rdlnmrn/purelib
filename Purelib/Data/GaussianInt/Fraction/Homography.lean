module

public import Purelib.Data.GaussianInt.Pair.Matrix
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.Ring

/-!
# Exact integral fraction images under homographies

The original displayed numerator and denominator form a homogeneous pair.
An integral matrix acts on that pair once. A certificate excluding the
affine pole supplies the new fraction's nonzero denominator, and the exact
value law identifies its homographic image without reducing either display.
-/

public section

namespace Purelib.Data.GaussianInt.Fraction

open Purelib.Data
open Purelib.Data.GaussianInt.Pair.Basic
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2

/-- Read the original fraction's retained numerator and denominator as a homogeneous pair. -/
@[expose] def asPair (fraction : Fraction) : ConvergentPair :=
  ⟨fraction.numerator, fraction.denominator⟩

/-- The transformed pair denominator is the affine denominator times the original displayed denominator. -/
theorem asPair_transform_denominator (fraction : Fraction) (matrix : Matrix GaussianInt) :
    GaussianInt.toGaussian (fraction.asPair.transform matrix).denominator =
      Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) fraction.value *
        GaussianInt.toGaussian fraction.denominator := by
  unfold asPair ConvergentPair.transform
  rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
  rewrite [← fraction.value_mul_denominator]
  unfold Homography.Basic.denominator Matrix.map
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The transformed pair numerator is the affine numerator times the original displayed denominator. -/
theorem asPair_transform_numerator (fraction : Fraction) (matrix : Matrix GaussianInt) :
    GaussianInt.toGaussian (fraction.asPair.transform matrix).numerator =
      Homography.Basic.numerator (Matrix.map GaussianInt.toGaussian matrix) fraction.value *
        GaussianInt.toGaussian fraction.denominator := by
  unfold asPair ConvergentPair.transform
  rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]
  rewrite [← fraction.value_mul_denominator]
  unfold Homography.Basic.numerator Matrix.map
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Excluding the affine pole certifies the exact transformed integral denominator as nonzero. -/
theorem asPair_transform_denominator_ne_zero (fraction : Fraction) (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) fraction.value ≠ 0) :
    (fraction.asPair.transform matrix).denominator ≠ 0 := by
  intro zero
  have embedded := congrArg GaussianInt.toGaussian zero
  rewrite [fraction.asPair_transform_denominator, GaussianInt.toGaussian_zero] at embedded
  exact (Gaussian.Field.mul_ne_zero_direct poleExcluded fraction.denominatorGaussianNonzero) embedded

/-- Construct the exact integral matrix image of the original displayed fraction.

The original homogeneous pair is transformed once and both output
coordinates use that same result. The affine-pole certificate supplies its
nonzero denominator; no normalization or reduction is performed.
-/
@[expose] def transform (fraction : Fraction) (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) fraction.value ≠ 0) :
    Fraction :=
  let pair := fraction.asPair.transform matrix
  { numerator := pair.numerator
    denominator := pair.denominator
    denominatorNonzero := fraction.asPair_transform_denominator_ne_zero matrix poleExcluded }

/-- The matrix image retains exactly the same complete transformed homogeneous pair. -/
theorem transform_asPair (fraction : Fraction) (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) fraction.value ≠ 0) :
    (fraction.transform matrix poleExcluded).asPair = fraction.asPair.transform matrix := rfl

/-- The constructed integral fraction has exactly the homographic value of the original displayed source. -/
theorem transform_value (fraction : Fraction) (matrix : Matrix GaussianInt)
    (poleExcluded : Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix) fraction.value ≠ 0) :
    (fraction.transform matrix poleExcluded).value =
      Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) fraction.value := by
  apply Fraction.value_eq_of_mul_den
  change Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian matrix) fraction.value *
      GaussianInt.toGaussian (fraction.asPair.transform matrix).denominator =
    GaussianInt.toGaussian (fraction.asPair.transform matrix).numerator
  rewrite [fraction.asPair_transform_denominator, fraction.asPair_transform_numerator]
  unfold Homography.Basic.homographic
  rewrite [← Gaussian.Basic.mul_assoc, Gaussian.Basic.mul_assoc
    (Homography.Basic.numerator (Matrix.map GaussianInt.toGaussian matrix) fraction.value),
    Gaussian.Field.inv_eq, Gaussian.Field.inv_mul _ poleExcluded, Gaussian.Basic.mul_one]
  rfl

end Purelib.Data.GaussianInt.Fraction
