module

public import Purelib.Data.GaussianInt.Pair.LinearCombination
public import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring

/-!
# Integral matrix transport of approximation pairs

A two-by-two Gaussian integral matrix acts on the original numerator and
denominator together. The coordinate laws retain the complete pairs and
their coefficient combinations, and the determinant law identifies the
index of every transported pair basis.
-/

public section

namespace Purelib.Data.GaussianInt.Pair.Basic.ConvergentPair

open Purelib.Data
open Purelib.Data.GaussianInt.Pair
open Purelib.LinearAlgebra.Coordinates2

/-- Apply the same integral matrix to the numerator and denominator column.

The upper row produces the new numerator and the lower row produces the
new denominator. Zero denominators remain valid pair data.
-/
@[expose] def transform (matrix : Matrix GaussianInt) (pair : ConvergentPair) :
    ConvergentPair where
  numerator := matrix.a * pair.numerator + matrix.b * pair.denominator
  denominator := matrix.c * pair.numerator + matrix.d * pair.denominator

/-- The identity matrix retains the original complete approximation pair. -/
theorem transform_identity (pair : ConvergentPair) :
    pair.transform Matrix.identity = pair := by
  apply LinearCombination.pair_ext <;> apply GaussianInt.ext <;>
    simp only [transform, Matrix.identity, GaussianInt.add_re, GaussianInt.add_im,
      GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.one_re, GaussianInt.one_im,
      GaussianInt.zero_re, GaussianInt.zero_im] <;> ring1

/-- Applying two matrices successively equals their column-action product. -/
theorem transform_transform (first second : Matrix GaussianInt) (pair : ConvergentPair) :
    (pair.transform first).transform second = pair.transform (Matrix.mul second first) := by
  apply LinearCombination.pair_ext <;> apply GaussianInt.ext <;>
    simp only [transform, Matrix.mul, GaussianInt.add_re, GaussianInt.add_im,
      GaussianInt.mul_re, GaussianInt.mul_im] <;> ring1

/-- Matrix transport retains the original integral coefficients of a pair combination. -/
theorem transform_linearCombination (matrix : Matrix GaussianInt)
    (left right : ConvergentPair) (leftCoefficient rightCoefficient : GaussianInt) :
    (LinearCombination.linearCombination left right leftCoefficient rightCoefficient).transform matrix =
      LinearCombination.linearCombination (left.transform matrix) (right.transform matrix)
        leftCoefficient rightCoefficient := by
  apply LinearCombination.pair_ext <;> apply GaussianInt.ext <;>
    simp only [transform, LinearCombination.linearCombination,
      GaussianInt.add_re, GaussianInt.add_im, GaussianInt.mul_re, GaussianInt.mul_im] <;> ring1

/-- Matrix transport commutes with scaling both original pair coordinates. -/
theorem transform_scalePair (matrix : Matrix GaussianInt) (coefficient : GaussianInt)
    (pair : ConvergentPair) :
    (LinearCombination.scalePair coefficient pair).transform matrix =
      LinearCombination.scalePair coefficient (pair.transform matrix) := by
  apply LinearCombination.pair_ext <;> apply GaussianInt.ext <;>
    simp only [transform, LinearCombination.scalePair, GaussianInt.add_re,
      GaussianInt.add_im, GaussianInt.mul_re, GaussianInt.mul_im] <;> ring1

/-- Transport multiplies the coefficient determinant by the matrix determinant. -/
theorem coefficientDeterminant_transform (matrix : Matrix GaussianInt)
    (left right : ConvergentPair) :
    LinearCombination.coefficientDeterminant (left.transform matrix) (right.transform matrix) =
      matrix.determinant * LinearCombination.coefficientDeterminant left right := by
  apply GaussianInt.ext <;>
    simp only [transform, LinearCombination.coefficientDeterminant, Basis.determinant,
      Matrix.determinant, GaussianInt.add_re, GaussianInt.add_im, GaussianInt.sub_re,
      GaussianInt.sub_im, GaussianInt.mul_re, GaussianInt.mul_im] <;> ring1

/-- The transported basis index is the product of the two determinant quadrances. -/
theorem coefficientIndexQuadrance_transform (matrix : Matrix GaussianInt)
    (left right : ConvergentPair) :
    LinearCombination.coefficientIndexQuadrance (left.transform matrix) (right.transform matrix) =
      GaussianInt.normNat matrix.determinant *
        LinearCombination.coefficientIndexQuadrance left right := by
  unfold LinearCombination.coefficientIndexQuadrance
  rewrite [coefficientDeterminant_transform, GaussianInt.normNat_mul]
  rfl

/-- A determinant-one matrix preserves the exact retained pair-basis determinant. -/
theorem coefficientDeterminant_transform_of_determinant_one (matrix : Matrix GaussianInt)
    (unitDeterminant : matrix.determinant = 1) (left right : ConvergentPair) :
    LinearCombination.coefficientDeterminant (left.transform matrix) (right.transform matrix) =
      LinearCombination.coefficientDeterminant left right := by
  rewrite [coefficientDeterminant_transform, unitDeterminant]
  exact GaussianInt.one_mul _

/-- Applying the adjugate after transport scales the original pair by the determinant. -/
theorem transform_adjugate (matrix : Matrix GaussianInt) (pair : ConvergentPair) :
    (pair.transform matrix).transform matrix.adjugate =
      LinearCombination.scalePair matrix.determinant pair := by
  apply LinearCombination.pair_ext <;> apply GaussianInt.ext <;>
    simp only [transform, Matrix.adjugate, Matrix.determinant, LinearCombination.scalePair,
      GaussianInt.add_re, GaussianInt.add_im, GaussianInt.sub_re, GaussianInt.sub_im,
      GaussianInt.neg_re, GaussianInt.neg_im, GaussianInt.mul_re, GaussianInt.mul_im] <;> ring1

/-- A determinant-one matrix has the original adjugate as an exact left inverse on pairs. -/
theorem transform_adjugate_of_determinant_one (matrix : Matrix GaussianInt)
    (unitDeterminant : matrix.determinant = 1) (pair : ConvergentPair) :
    (pair.transform matrix).transform matrix.adjugate = pair := by
  rewrite [transform_adjugate, unitDeterminant]
  apply LinearCombination.pair_ext <;> apply GaussianInt.ext <;>
    simp only [LinearCombination.scalePair, GaussianInt.mul_re, GaussianInt.mul_im,
      GaussianInt.one_re, GaussianInt.one_im] <;> ring1

/-- A determinant-one matrix cannot identify two distinct original pairs. -/
theorem eq_of_transform_eq (matrix : Matrix GaussianInt)
    (unitDeterminant : matrix.determinant = 1) {left right : ConvergentPair}
    (same : left.transform matrix = right.transform matrix) : left = right := by
  have recovered := congrArg (fun pair => pair.transform matrix.adjugate) same
  rewrite [transform_adjugate_of_determinant_one matrix unitDeterminant,
    transform_adjugate_of_determinant_one matrix unitDeterminant] at recovered
  exact recovered

end Purelib.Data.GaussianInt.Pair.Basic.ConvergentPair
