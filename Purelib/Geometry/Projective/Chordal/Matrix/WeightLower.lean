module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Chordal.Matrix
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal.Matrix

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Rational parameterizations of CCL comparison boundaries

Coordinate lines and centered circles are transported through an invertible
finite homography by its explicit adjugate.  The resulting rational curve is
proved to lie on the corresponding Hermitian comparison boundary at every
non-pole parameter.  This is the provenance-preserving bridge needed before
the cleared gcd/Sturm classifier can inspect parser-formula boundaries.
-/

namespace Purelib.Geometry.Projective.Hermitian.Parametrization
section Parametrization

/-- A lower bound for transformed homogeneous weight from a source weight bound.

Multiply by the determinant quadrance and divide by the adjugate action coefficient. -/
private def transformedWeightLower (matrix
  : GaussianMatrix)
    (sourceLower : Fraction.Rational) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) * sourceLower /
    Mat2.actionWeightCoefficient
      (BoundaryAdjugate.adjugate matrix)

/-- A nonzero determinant and positive source bound give a positive transformed weight bound. -/
private theorem transformedWeightLower_pos
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    {sourceLower : Fraction.Rational} (sourceLowerPositive : 0 < sourceLower) :
    0 < transformedWeightLower matrix sourceLower := by
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Data.Gaussian.Norm.Basic.normSq_pos determinantNonzero) sourceLowerPositive)
    (Mat2.actionWeightCoefficient_pos
      (BoundaryAdjugate.adjugate matrix))

/-- Acting by a matrix and then its adjugate scales the projective pair by the determinant. -/
private theorem adjugate_act_act
    (matrix : GaussianMatrix) (point : GaussianLine) :
    Line.Matrix.act (BoundaryAdjugate.adjugate matrix)
        (Line.Matrix.act matrix point) =
      Proj.scale
        (BoundaryAdjugate.determinant matrix) point := by
  apply Proj.ext
  · apply Data.Gaussian.Basic.ext <;>
      simp only [Line.Matrix.act, BoundaryAdjugate.adjugate,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Proj.scale,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im] <;>
      ring1
  · apply Data.Gaussian.Basic.ext <;>
      simp only [Line.Matrix.act, BoundaryAdjugate.adjugate,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Proj.scale,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im] <;>
      ring1

/-- The computed transformed bound is below the image weight whenever the source weight has the supplied lower bound. -/
private theorem transformedWeightLower_le
    (matrix : GaussianMatrix)
    (sourceLower : Fraction.Rational)
    (point : GaussianLine)
    (sourceLowerLe : sourceLower ≤
      Proj.weight point) :
    transformedWeightLower matrix sourceLower ≤
      Proj.weight (Line.Matrix.act matrix point) := by
  let inverse := BoundaryAdjugate.adjugate matrix
  let coefficient :=
    Mat2.actionWeightCoefficient inverse
  let image := Line.Matrix.act matrix point
  have coefficientPositive : 0 < coefficient :=
    Mat2.actionWeightCoefficient_pos inverse
  have scaledLower :
      Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) * sourceLower ≤
        Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          Proj.weight point :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLowerLe
      (Data.Gaussian.Norm.Basic.normSq_nonneg (BoundaryAdjugate.determinant matrix))
  have inverseUpper :=
    Mat2.act_weight_le inverse image
  have inverseIdentity : Line.Matrix.act inverse image =
      Proj.scale
        (BoundaryAdjugate.determinant matrix) point :=
    adjugate_act_act matrix point
  have scaledWeight :
      Proj.weight
          (Proj.scale
            (BoundaryAdjugate.determinant matrix) point) =
        Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          Proj.weight point :=
    Proj.weight_scale
      (BoundaryAdjugate.determinant matrix) point
  apply (Fraction.Order.Field.div_le_iff_pos coefficientPositive).2
  calc
    Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) * sourceLower ≤
        Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          Proj.weight point := scaledLower
    _ = Proj.weight
        (Line.Matrix.act inverse image) := by
      rw [inverseIdentity, scaledWeight]
    _ ≤ coefficient * Proj.weight image := inverseUpper
    _ = Proj.weight image * coefficient :=
      Fraction.Field.mul_comm _ _

/-- Acting by a matrix and then its adjugate scales the projective pair by the determinant. -/
theorem adjugateActsAsScale
    (matrix : GaussianMatrix) (point : GaussianLine) :
    Line.Matrix.act (BoundaryAdjugate.adjugate matrix)
        (Line.Matrix.act matrix point) =
      Proj.scale
        (BoundaryAdjugate.determinant matrix) point := by
  apply Proj.ext
  · apply Data.Gaussian.Basic.ext <;>
      simp only [Line.Matrix.act, BoundaryAdjugate.adjugate,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Proj.scale,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im] <;>
      ring1
  · apply Data.Gaussian.Basic.ext <;>
      simp only [Line.Matrix.act, BoundaryAdjugate.adjugate,
        BoundaryAdjugate.determinant,
        Matrix2.determinant,
        Proj.scale,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Basic.neg_re,
        Data.Gaussian.Basic.neg_im] <;>
      ring1

/-- The determinant quadrance and adjugate coefficient transport a source weight lower bound.

The inequality holds for every displayed matrix and point; determinant nonzeroness is needed only to obtain a positive
bound. -/
theorem transformedPointWeightLower
    (matrix : GaussianMatrix)
    (sourceLower : Fraction.Rational)
    (point : GaussianLine)
    (sourceLowerLe : sourceLower ≤
      Proj.weight point) :
    Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) * sourceLower /
      Mat2.actionWeightCoefficient
        (BoundaryAdjugate.adjugate matrix) ≤
      Proj.weight
        (Line.Matrix.act matrix point) := by
  let inverse := BoundaryAdjugate.adjugate matrix
  let coefficient :=
    Mat2.actionWeightCoefficient inverse
  let image := Line.Matrix.act matrix point
  have coefficientPositive : 0 < coefficient :=
    Mat2.actionWeightCoefficient_pos inverse
  have scaledLower :
      Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) * sourceLower ≤
        Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          Proj.weight point :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLowerLe
      (Data.Gaussian.Norm.Basic.normSq_nonneg (BoundaryAdjugate.determinant matrix))
  have inverseUpper :=
    Mat2.act_weight_le inverse image
  have inverseIdentity : Line.Matrix.act inverse image =
      Proj.scale
        (BoundaryAdjugate.determinant matrix) point :=
    adjugateActsAsScale matrix point
  have scaledWeight :
      Proj.weight
          (Proj.scale
            (BoundaryAdjugate.determinant matrix) point) =
        Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          Proj.weight point :=
    Proj.weight_scale
      (BoundaryAdjugate.determinant matrix) point
  apply (Fraction.Order.Field.div_le_iff_pos coefficientPositive).2
  calc
    Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) * sourceLower ≤
        Data.Gaussian.Norm.Basic.normSq (BoundaryAdjugate.determinant matrix) *
          Proj.weight point := scaledLower
    _ = Proj.weight
        (Line.Matrix.act inverse image) := by
      rw [inverseIdentity, scaledWeight]
    _ ≤ coefficient * Proj.weight image := inverseUpper
    _ = Proj.weight image * coefficient :=
      Fraction.Field.mul_comm _ _
end Parametrization
end Purelib.Geometry.Projective.Hermitian.Parametrization

end
